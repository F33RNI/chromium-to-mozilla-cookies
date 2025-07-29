#!/usr/bin/env python3

# Simple zero-dependency script that converts and decrypts cookies from chromium-based browser
# for importing into Mozilla's firefox-based browsers

import argparse
import base64
import collections.abc
import contextlib
import functools
import hashlib
import json
import os
import re
import shlex
import shutil
import sqlite3
import struct
import subprocess
import sys
import tempfile
from enum import Enum, auto
from math import ceil
from typing import Any

##############################################################################################
#                                                                                            #
# CODE BELOW IS TAKEN FROM <https://github.com/yt-dlp/yt-dlp/blob/master/yt_dlp/cookies.py>, #
# <https://github.com/yt-dlp/yt-dlp/blob/master/yt_dlp/aes.py> AND                           #
# <https://github.com/yt-dlp/yt-dlp/blob/master/yt_dlp/compat/__init__.py>                   #
#                                                                                            #
# And modified for the <https://github.com/F33RNI/chromium-to-firefox-cookies> project       #
#                                                                                            #
# See code around main() (at the end of this file) for more info                             #
#                                                                                            #
# ORIGINAL CODE IS LICENSED UNDER THE UNLICENSE LICENSE. PLEASE VIEW ORIGINAL YT-DLP REPO    #
# <https://github.com/yt-dlp/yt-dlp> FOR MORE INFO                                           #
#                                                                                            #
##############################################################################################

CHROMIUM_BASED_BROWSERS = {"brave", "chrome", "chromium", "edge", "opera", "vivaldi", "whale"}


def extract_chrome_cookies(
    browser_name: str, profile: str | None = None, keyring: str | None = None
) -> list[list[Any]]:
    """Extracts and decrypts cookies from chromium-based browser
    Original code is from yt-dlp: <https://github.com/yt-dlp/yt-dlp>

    Args:
        browser_name (str): one of CHROMIUM_BASED_BROWSERS
        profile (str, optional): name/path of the profile to load cookies from. Defaults to None
        keyring (str, optional): keyring name. Defaults to None

    Raises:
        Exception in case of error

    Returns:
        list[list[Any]]: list of raw cookies, where each cookies is a list of column values:
            creation_utc, host_key, name, value, encrypted_value, path, expires_utc, is_secure, is_httponly,
            last_access_utc, samesite, source_scheme
    """
    config = _get_chromium_based_browser_settings(browser_name)

    if profile is None:
        search_root = config["browser_dir"]
    elif _is_path(profile):
        search_root = profile
        config["browser_dir"] = os.path.dirname(profile) if config["supports_profiles"] else profile
    else:
        if config["supports_profiles"]:
            search_root = os.path.join(config["browser_dir"], profile)
        else:
            print(f"{browser_name} does not support profiles")
            search_root = config["browser_dir"]

    cookie_database_path = _newest(_find_files(search_root, "Cookies"))
    if cookie_database_path is None:
        raise FileNotFoundError(f'could not find {browser_name} cookies database in "{search_root}"')
    print(f'Extracting cookies from: "{cookie_database_path}"')

    with tempfile.TemporaryDirectory(prefix="yt_dlp") as tmpdir:
        cursor = None
        try:
            cursor = _open_database_copy(cookie_database_path, tmpdir)

            # meta_version is necessary to determine if we need to trim the hash prefix from the cookies
            # Ref: https://chromium.googlesource.com/chromium/src/+/b02dcebd7cafab92770734dc2bc317bd07f1d891/net/extras/sqlite/sqlite_persistent_cookie_store.cc#223
            meta_version = int(cursor.execute('SELECT value FROM meta WHERE key = "version"').fetchone()[0])
            decryptor = get_cookie_decryptor(
                config["browser_dir"], config["keyring_name"], keyring=keyring, meta_version=meta_version
            )

            cursor.connection.text_factory = bytes
            column_names = _get_column_names(cursor, "cookies")
            secure_column = "is_secure" if "is_secure" in column_names else "secure"
            cursor.execute(
                f"SELECT creation_utc, host_key, name, value, encrypted_value, path, expires_utc, {secure_column}, "
                "is_httponly, last_access_utc, samesite, source_scheme FROM cookies"
            )
            cookies_raw = []
            failed_cookies = 0
            unencrypted_cookies = 0

            table = cursor.fetchall()
            for line in table:
                if not line:
                    failed_cookies += 1
                    continue

                # Convert into list and decrypt value
                line = list(line)
                value = line[3]
                encrypted_value = line[4]
                is_encrypted = not value and encrypted_value
                if is_encrypted:
                    value = decryptor.decrypt(encrypted_value)
                    line[3] = value
                else:
                    value = value.decode("utf-8")

                # Check
                if not value:
                    failed_cookies += 1
                    continue
                elif not is_encrypted:
                    unencrypted_cookies += 1

                # Append line
                cookies_raw.append(line)

            if failed_cookies > 0:
                failed_message = f" ({failed_cookies} could not be decrypted)"
            else:
                failed_message = ""
            print(f"Extracted {len(cookies_raw)} cookies from {browser_name}{failed_message}")

            counts = decryptor._cookie_counts.copy()
            counts["unencrypted"] = unencrypted_cookies
            print(f"cookie version breakdown: {counts}")
            return cookies_raw
        except PermissionError as error:
            if os.name == "nt" and error.errno == 13:
                message = "Could not copy Chrome cookie database. See  https://github.com/yt-dlp/yt-dlp/issues/7271  for more info"
                print(f"ERROR: Download error: {message}")
            else:
                print(f"Got PermissionError: {error}")
            sys.exit(-1)
        finally:
            if cursor is not None:
                cursor.connection.close()


_WINDOWS_QUOTE_TRANS = str.maketrans({'"': R"\""})
_CMD_QUOTE_TRANS = str.maketrans(
    {
        # Keep quotes balanced by replacing them with `""` instead of `\\"`
        '"': '""',
        # These require an env-variable `=` containing `"^\n\n"` (set in `utils.Popen`)
        # `=` should be unique since variables containing `=` cannot be set using cmd
        "\n": "%=%",
        "\r": "%=%",
        # Use zero length variable replacement so `%` doesn't get expanded
        # `cd` is always set as long as extensions are enabled (`/E:ON` in `utils.Popen`)
        "%": "%%cd:~,%",
    }
)


class NO_DEFAULT:
    pass


def is_iterable_like(x, allowed_types=collections.abc.Iterable, blocked_types=NO_DEFAULT):
    if blocked_types is NO_DEFAULT:
        blocked_types = (str, bytes, collections.abc.Mapping)
    return isinstance(x, allowed_types) and not isinstance(x, blocked_types)


def variadic(x, allowed_types=NO_DEFAULT):
    if not isinstance(allowed_types, (tuple, type)):
        print("allowed_types should be a tuple or a type")
        allowed_types = tuple(allowed_types)
    return x if is_iterable_like(x, blocked_types=allowed_types) else (x,)  # pyright: ignore


def shell_quote(args, *, shell=False):
    args = list(variadic(args))

    if os.name != "nt":
        return shlex.join(args)

    trans = _CMD_QUOTE_TRANS if shell else _WINDOWS_QUOTE_TRANS
    return " ".join(
        (
            s
            if re.fullmatch(r"[\w#$*\-+./:?@\\]+", s, re.ASCII)
            else re.sub(r'(\\+)("|$)', r"\1\1\2", s).translate(trans).join('""')
        )
        for s in args
    )


class Popen(subprocess.Popen):
    if sys.platform == "win32":
        _startupinfo = subprocess.STARTUPINFO()
        _startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
    else:
        _startupinfo = None

    @staticmethod
    def _fix_pyinstaller_issues(env):
        if not hasattr(sys, "_MEIPASS"):
            return

        # Force spawning independent subprocesses for exes bundled with PyInstaller>=6.10
        # Ref: https://pyinstaller.org/en/v6.10.0/CHANGES.html#incompatible-changes
        #      https://github.com/yt-dlp/yt-dlp/issues/11259
        env["PYINSTALLER_RESET_ENVIRONMENT"] = "1"

        # Restore LD_LIBRARY_PATH when using PyInstaller
        # Ref: https://pyinstaller.org/en/v6.10.0/runtime-information.html#ld-library-path-libpath-considerations
        #      https://github.com/yt-dlp/yt-dlp/issues/4573
        def _fix(key):
            orig = env.get(f"{key}_ORIG")
            if orig is None:
                env.pop(key, None)
            else:
                env[key] = orig

        _fix("LD_LIBRARY_PATH")  # Linux
        _fix("DYLD_LIBRARY_PATH")  # macOS

    def __init__(self, args, *remaining, env=None, text=False, shell=False, **kwargs):
        if env is None:
            env = os.environ.copy()
        self._fix_pyinstaller_issues(env)

        self.__text_mode = kwargs.get("encoding") or kwargs.get("errors") or text or kwargs.get("universal_newlines")
        if text is True:
            kwargs["universal_newlines"] = True  # For 3.6 compatibility
            kwargs.setdefault("encoding", "utf-8")
            kwargs.setdefault("errors", "replace")

        if shell and os.name == "nt" and kwargs.get("executable") is None:
            if not isinstance(args, str):
                args = shell_quote(args, shell=True)
            shell = False
            # Set variable for `cmd.exe` newline escaping (see `utils.shell_quote`)
            env["="] = '"^\n\n"'
            args = f'{self.__comspec()} /Q /S /D /V:OFF /E:ON /C "{args}"'

        super().__init__(args, *remaining, env=env, shell=shell, **kwargs, startupinfo=self._startupinfo)

    def __comspec(self):
        comspec = os.environ.get("ComSpec") or os.path.join(os.environ.get("SystemRoot", ""), "System32", "cmd.exe")
        if os.path.isabs(comspec):
            return comspec
        raise FileNotFoundError("shell not found: neither %ComSpec% nor %SystemRoot% is set")

    def communicate_or_kill(self, *args, **kwargs):
        try:
            return self.communicate(*args, **kwargs)
        except BaseException:  # Including KeyboardInterrupt
            self.kill(timeout=None)  # pyright: ignore
            raise

    def kill(self, *, timeout=0):
        super().kill()
        if timeout != 0:
            self.wait(timeout=timeout)

    @classmethod
    def run(cls, *args, timeout=None, **kwargs):
        with cls(*args, **kwargs) as proc:
            default = "" if proc.__text_mode else b""
            stdout, stderr = proc.communicate_or_kill(timeout=timeout)
            return stdout or default, stderr or default, proc.returncode


def _get_chromium_based_browser_settings(browser_name):
    # https://chromium.googlesource.com/chromium/src/+/HEAD/docs/user_data_dir.md
    if sys.platform in ("cygwin", "win32"):
        appdata_local = os.path.expandvars("%LOCALAPPDATA%")
        appdata_roaming = os.path.expandvars("%APPDATA%")
        browser_dir = {
            "brave": os.path.join(appdata_local, R"BraveSoftware\Brave-Browser\User Data"),
            "chrome": os.path.join(appdata_local, R"Google\Chrome\User Data"),
            "chromium": os.path.join(appdata_local, R"Chromium\User Data"),
            "edge": os.path.join(appdata_local, R"Microsoft\Edge\User Data"),
            "opera": os.path.join(appdata_roaming, R"Opera Software\Opera Stable"),
            "vivaldi": os.path.join(appdata_local, R"Vivaldi\User Data"),
            "whale": os.path.join(appdata_local, R"Naver\Naver Whale\User Data"),
        }[browser_name]

    elif sys.platform == "darwin":
        appdata = os.path.expanduser("~/Library/Application Support")
        browser_dir = {
            "brave": os.path.join(appdata, "BraveSoftware/Brave-Browser"),
            "chrome": os.path.join(appdata, "Google/Chrome"),
            "chromium": os.path.join(appdata, "Chromium"),
            "edge": os.path.join(appdata, "Microsoft Edge"),
            "opera": os.path.join(appdata, "com.operasoftware.Opera"),
            "vivaldi": os.path.join(appdata, "Vivaldi"),
            "whale": os.path.join(appdata, "Naver/Whale"),
        }[browser_name]

    else:
        config = _config_home()
        browser_dir = {
            "brave": os.path.join(config, "BraveSoftware/Brave-Browser"),
            "chrome": os.path.join(config, "google-chrome"),
            "chromium": os.path.join(config, "chromium"),
            "edge": os.path.join(config, "microsoft-edge"),
            "opera": os.path.join(config, "opera"),
            "vivaldi": os.path.join(config, "vivaldi"),
            "whale": os.path.join(config, "naver-whale"),
        }[browser_name]

    # Linux keyring names can be determined by snooping on dbus while opening the browser in KDE:
    # dbus-monitor "interface='org.kde.KWallet'" "type=method_return"
    keyring_name = {
        "brave": "Brave",
        "chrome": "Chrome",
        "chromium": "Chromium",
        "edge": "Microsoft Edge" if sys.platform == "darwin" else "Chromium",
        "opera": "Opera" if sys.platform == "darwin" else "Chromium",
        "vivaldi": "Vivaldi" if sys.platform == "darwin" else "Chrome",
        "whale": "Whale",
    }[browser_name]

    browsers_without_profiles = {"opera"}

    return {
        "browser_dir": browser_dir,
        "keyring_name": keyring_name,
        "supports_profiles": browser_name not in browsers_without_profiles,
    }


class ChromeCookieDecryptor:
    """
    Overview:

        Linux:
        - cookies are either v10 or v11
            - v10: AES-CBC encrypted with a fixed key
                - also attempts empty password if decryption fails
            - v11: AES-CBC encrypted with an OS protected key (keyring)
                - also attempts empty password if decryption fails
            - v11 keys can be stored in various places depending on the activate desktop environment [2]

        Mac:
        - cookies are either v10 or not v10
            - v10: AES-CBC encrypted with an OS protected key (keyring) and more key derivation iterations than linux
            - not v10: 'old data' stored as plaintext

        Windows:
        - cookies are either v10 or not v10
            - v10: AES-GCM encrypted with a key which is encrypted with DPAPI
            - not v10: encrypted with DPAPI

    Sources:
    - [1] https://chromium.googlesource.com/chromium/src/+/refs/heads/main/components/os_crypt/
    - [2] https://chromium.googlesource.com/chromium/src/+/refs/heads/main/components/os_crypt/sync/key_storage_linux.cc
        - KeyStorageLinux::CreateService
    """

    _cookie_counts = {}

    def decrypt(self, encrypted_value):
        raise NotImplementedError("Must be implemented by sub classes")


def get_cookie_decryptor(browser_root, browser_keyring_name, *, keyring=None, meta_version=None):
    if sys.platform == "darwin":
        return MacChromeCookieDecryptor(browser_keyring_name, meta_version=meta_version)
    elif sys.platform in ("win32", "cygwin"):
        return WindowsChromeCookieDecryptor(browser_root, meta_version=meta_version)
    return LinuxChromeCookieDecryptor(browser_keyring_name, keyring=keyring, meta_version=meta_version)


class LinuxChromeCookieDecryptor(ChromeCookieDecryptor):
    def __init__(self, browser_keyring_name, *, keyring=None, meta_version=None):
        self._v10_key = self.derive_key(b"peanuts")
        self._empty_key = self.derive_key(b"")
        self._cookie_counts = {"v10": 0, "v11": 0, "other": 0}
        self._browser_keyring_name = browser_keyring_name
        self._keyring = keyring
        self._meta_version = meta_version or 0

    @functools.cached_property
    def _v11_key(self):
        password = _get_linux_keyring_password(self._browser_keyring_name, self._keyring)
        return None if password is None else self.derive_key(password)

    @staticmethod
    def derive_key(password):
        # values from
        # https://chromium.googlesource.com/chromium/src/+/refs/heads/main/components/os_crypt/sync/os_crypt_linux.cc
        return pbkdf2_sha1(password, salt=b"saltysalt", iterations=1, key_length=16)

    def decrypt(self, encrypted_value):
        """

        following the same approach as the fix in [1]: if cookies fail to decrypt then attempt to decrypt
        with an empty password. The failure detection is not the same as what chromium uses so the
        results won't be perfect

        References:
            - [1] https://chromium.googlesource.com/chromium/src/+/bbd54702284caca1f92d656fdcadf2ccca6f4165%5E%21/
                - a bugfix to try an empty password as a fallback
        """
        version = encrypted_value[:3]
        ciphertext = encrypted_value[3:]

        if version == b"v10":
            self._cookie_counts["v10"] += 1
            return _decrypt_aes_cbc_multi(
                ciphertext, (self._v10_key, self._empty_key), hash_prefix=self._meta_version >= 24
            )

        elif version == b"v11":
            self._cookie_counts["v11"] += 1
            if self._v11_key is None:
                print("cannot decrypt v11 cookies: no key found")
                return None
            return _decrypt_aes_cbc_multi(
                ciphertext, (self._v11_key, self._empty_key), hash_prefix=self._meta_version >= 24
            )

        else:
            print(f'unknown cookie version: "{version}"')
            self._cookie_counts["other"] += 1
            return None


class MacChromeCookieDecryptor(ChromeCookieDecryptor):
    def __init__(self, browser_keyring_name, meta_version=None):
        password = _get_mac_keyring_password(browser_keyring_name)
        self._v10_key = None if password is None else self.derive_key(password)
        self._cookie_counts = {"v10": 0, "other": 0}
        self._meta_version = meta_version or 0

    @staticmethod
    def derive_key(password):
        # values from
        # https://chromium.googlesource.com/chromium/src/+/refs/heads/main/components/os_crypt/sync/os_crypt_mac.mm
        return pbkdf2_sha1(password, salt=b"saltysalt", iterations=1003, key_length=16)

    def decrypt(self, encrypted_value):
        version = encrypted_value[:3]
        ciphertext = encrypted_value[3:]

        if version == b"v10":
            self._cookie_counts["v10"] += 1
            if self._v10_key is None:
                print("cannot decrypt v10 cookies: no key found")
                return None

            return _decrypt_aes_cbc_multi(ciphertext, (self._v10_key,), hash_prefix=self._meta_version >= 24)

        else:
            self._cookie_counts["other"] += 1
            # other prefixes are considered 'old data' which were stored as plaintext
            # https://chromium.googlesource.com/chromium/src/+/refs/heads/main/components/os_crypt/sync/os_crypt_mac.mm
            return encrypted_value


class WindowsChromeCookieDecryptor(ChromeCookieDecryptor):
    def __init__(self, browser_root, meta_version=None):
        self._v10_key = _get_windows_v10_key(browser_root)
        self._cookie_counts = {"v10": 0, "other": 0}
        self._meta_version = meta_version or 0

    def decrypt(self, encrypted_value):
        version = encrypted_value[:3]
        ciphertext = encrypted_value[3:]

        if version == b"v10":
            self._cookie_counts["v10"] += 1
            if self._v10_key is None:
                print("cannot decrypt v10 cookies: no key found")
                return None

            # https://chromium.googlesource.com/chromium/src/+/refs/heads/main/components/os_crypt/sync/os_crypt_win.cc
            #   kNonceLength
            nonce_length = 96 // 8
            # boringssl
            #   EVP_AEAD_AES_GCM_TAG_LEN
            authentication_tag_length = 16

            raw_ciphertext = ciphertext
            nonce = raw_ciphertext[:nonce_length]
            ciphertext = raw_ciphertext[nonce_length:-authentication_tag_length]
            authentication_tag = raw_ciphertext[-authentication_tag_length:]

            return _decrypt_aes_gcm(
                ciphertext, self._v10_key, nonce, authentication_tag, hash_prefix=self._meta_version >= 24
            )

        else:
            self._cookie_counts["other"] += 1
            # any other prefix means the data is DPAPI encrypted
            # https://chromium.googlesource.com/chromium/src/+/refs/heads/main/components/os_crypt/sync/os_crypt_win.cc
            return _decrypt_windows_dpapi(encrypted_value).decode()


class ParserError(Exception):
    pass


class DataParser:
    def __init__(self, data):
        self._data = data
        self.cursor = 0

    def read_bytes(self, num_bytes):
        if num_bytes < 0:
            raise ParserError(f"invalid read of {num_bytes} bytes")
        end = self.cursor + num_bytes
        if end > len(self._data):
            raise ParserError("reached end of input")
        data = self._data[self.cursor : end]
        self.cursor = end
        return data

    def expect_bytes(self, expected_value, message):
        value = self.read_bytes(len(expected_value))
        if value != expected_value:
            raise ParserError(f"unexpected value: {value} != {expected_value} ({message})")

    def read_uint(self, big_endian=False):
        data_format = ">I" if big_endian else "<I"
        return struct.unpack(data_format, self.read_bytes(4))[0]

    def read_double(self, big_endian=False):
        data_format = ">d" if big_endian else "<d"
        return struct.unpack(data_format, self.read_bytes(8))[0]

    def read_cstring(self):
        buffer = []
        while True:
            c = self.read_bytes(1)
            if c == b"\x00":
                return b"".join(buffer).decode()
            else:
                buffer.append(c)

    def skip(self, num_bytes, description="unknown"):
        if num_bytes > 0:
            print(f"skipping {num_bytes} bytes ({description}): {self.read_bytes(num_bytes)!r}")
        elif num_bytes < 0:
            raise ParserError(f"invalid skip of {num_bytes} bytes")

    def skip_to(self, offset, description="unknown"):
        self.skip(offset - self.cursor, description)

    def skip_to_end(self, description="unknown"):
        self.skip_to(len(self._data), description)


class _LinuxDesktopEnvironment(Enum):
    """
    https://chromium.googlesource.com/chromium/src/+/refs/heads/main/base/nix/xdg_util.h
    DesktopEnvironment
    """

    OTHER = auto()
    CINNAMON = auto()
    DEEPIN = auto()
    GNOME = auto()
    KDE3 = auto()
    KDE4 = auto()
    KDE5 = auto()
    KDE6 = auto()
    PANTHEON = auto()
    UKUI = auto()
    UNITY = auto()
    XFCE = auto()
    LXQT = auto()


class _LinuxKeyring(Enum):
    """
    https://chromium.googlesource.com/chromium/src/+/refs/heads/main/components/os_crypt/sync/key_storage_util_linux.h
    SelectedLinuxBackend
    """

    KWALLET = auto()  # KDE4
    KWALLET5 = auto()
    KWALLET6 = auto()
    GNOMEKEYRING = auto()
    BASICTEXT = auto()


SUPPORTED_KEYRINGS = _LinuxKeyring.__members__.keys()


def _get_linux_desktop_environment(env):
    """
    https://chromium.googlesource.com/chromium/src/+/refs/heads/main/base/nix/xdg_util.cc
    GetDesktopEnvironment
    """
    xdg_current_desktop = env.get("XDG_CURRENT_DESKTOP", None)
    desktop_session = env.get("DESKTOP_SESSION", "")
    if xdg_current_desktop is not None:
        for part in map(str.strip, xdg_current_desktop.split(":")):
            if part == "Unity":
                if "gnome-fallback" in desktop_session:
                    return _LinuxDesktopEnvironment.GNOME
                else:
                    return _LinuxDesktopEnvironment.UNITY
            elif part == "Deepin":
                return _LinuxDesktopEnvironment.DEEPIN
            elif part == "GNOME":
                return _LinuxDesktopEnvironment.GNOME
            elif part == "X-Cinnamon":
                return _LinuxDesktopEnvironment.CINNAMON
            elif part == "KDE":
                kde_version = env.get("KDE_SESSION_VERSION", None)
                if kde_version == "5":
                    return _LinuxDesktopEnvironment.KDE5
                elif kde_version == "6":
                    return _LinuxDesktopEnvironment.KDE6
                elif kde_version == "4":
                    return _LinuxDesktopEnvironment.KDE4
                else:
                    print(f'unknown KDE version: "{kde_version}". Assuming KDE4')
                    return _LinuxDesktopEnvironment.KDE4
            elif part == "Pantheon":
                return _LinuxDesktopEnvironment.PANTHEON
            elif part == "XFCE":
                return _LinuxDesktopEnvironment.XFCE
            elif part == "UKUI":
                return _LinuxDesktopEnvironment.UKUI
            elif part == "LXQt":
                return _LinuxDesktopEnvironment.LXQT
        print(f'XDG_CURRENT_DESKTOP is set to an unknown value: "{xdg_current_desktop}"')

    if desktop_session == "deepin":
        return _LinuxDesktopEnvironment.DEEPIN
    elif desktop_session in ("mate", "gnome"):
        return _LinuxDesktopEnvironment.GNOME
    elif desktop_session in ("kde4", "kde-plasma"):
        return _LinuxDesktopEnvironment.KDE4
    elif desktop_session == "kde":
        if "KDE_SESSION_VERSION" in env:
            return _LinuxDesktopEnvironment.KDE4
        else:
            return _LinuxDesktopEnvironment.KDE3
    elif "xfce" in desktop_session or desktop_session == "xubuntu":
        return _LinuxDesktopEnvironment.XFCE
    elif desktop_session == "ukui":
        return _LinuxDesktopEnvironment.UKUI
    else:
        print(f'DESKTOP_SESSION is set to an unknown value: "{desktop_session}"')

    if "GNOME_DESKTOP_SESSION_ID" in env:
        return _LinuxDesktopEnvironment.GNOME
    elif "KDE_FULL_SESSION" in env:
        if "KDE_SESSION_VERSION" in env:
            return _LinuxDesktopEnvironment.KDE4
        else:
            return _LinuxDesktopEnvironment.KDE3

    return _LinuxDesktopEnvironment.OTHER


def _choose_linux_keyring():
    """
    SelectBackend in [1]

    There is currently support for forcing chromium to use BASIC_TEXT by creating a file called
    `Disable Local Encryption` [1] in the user data dir. The function to write this file (`WriteBackendUse()` [1])
    does not appear to be called anywhere other than in tests, so the user would have to create this file manually
    and so would be aware enough to tell yt-dlp to use the BASIC_TEXT keyring.

    References:
        - [1] https://chromium.googlesource.com/chromium/src/+/refs/heads/main/components/os_crypt/sync/key_storage_util_linux.cc
    """
    desktop_environment = _get_linux_desktop_environment(os.environ)
    print(f"detected desktop environment: {desktop_environment.name}")
    if desktop_environment == _LinuxDesktopEnvironment.KDE4:
        linux_keyring = _LinuxKeyring.KWALLET
    elif desktop_environment == _LinuxDesktopEnvironment.KDE5:
        linux_keyring = _LinuxKeyring.KWALLET5
    elif desktop_environment == _LinuxDesktopEnvironment.KDE6:
        linux_keyring = _LinuxKeyring.KWALLET6
    elif desktop_environment in (
        _LinuxDesktopEnvironment.KDE3,
        _LinuxDesktopEnvironment.LXQT,
        _LinuxDesktopEnvironment.OTHER,
    ):
        linux_keyring = _LinuxKeyring.BASICTEXT
    else:
        linux_keyring = _LinuxKeyring.GNOMEKEYRING
    return linux_keyring


def _get_kwallet_network_wallet(keyring):
    """The name of the wallet used to store network passwords.

    https://chromium.googlesource.com/chromium/src/+/refs/heads/main/components/os_crypt/sync/kwallet_dbus.cc
    KWalletDBus::NetworkWallet
    which does a dbus call to the following function:
    https://api.kde.org/frameworks/kwallet/html/classKWallet_1_1Wallet.html
    Wallet::NetworkWallet
    """
    default_wallet = "kdewallet"
    try:
        if keyring == _LinuxKeyring.KWALLET:
            service_name = "org.kde.kwalletd"
            wallet_path = "/modules/kwalletd"
        elif keyring == _LinuxKeyring.KWALLET5:
            service_name = "org.kde.kwalletd5"
            wallet_path = "/modules/kwalletd5"
        elif keyring == _LinuxKeyring.KWALLET6:
            service_name = "org.kde.kwalletd6"
            wallet_path = "/modules/kwalletd6"
        else:
            raise ValueError(keyring)

        stdout, _, returncode = Popen.run(
            [
                "dbus-send",
                "--session",
                "--print-reply=literal",
                f"--dest={service_name}",
                wallet_path,
                "org.kde.KWallet.networkWallet",
            ],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
        )

        if returncode:
            print("failed to read NetworkWallet")
            return default_wallet
        else:
            print(f'NetworkWallet = "{stdout.strip()}"')
            return stdout.strip()
    except Exception as e:
        print(f"exception while obtaining NetworkWallet: {e}")
        return default_wallet


def _get_kwallet_password(browser_keyring_name, keyring):
    print(f"using kwallet-query to obtain password from {keyring.name}")

    if shutil.which("kwallet-query") is None:
        print(
            "kwallet-query command not found. KWallet and kwallet-query "
            "must be installed to read from KWallet. kwallet-query should be"
            "included in the kwallet package for your distribution"
        )
        return b""

    network_wallet = _get_kwallet_network_wallet(keyring)

    try:
        stdout, _, returncode = Popen.run(
            [
                "kwallet-query",
                "--read-password",
                f"{browser_keyring_name} Safe Storage",
                "--folder",
                f"{browser_keyring_name} Keys",
                network_wallet,
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
        )

        if returncode:
            print(
                f"kwallet-query failed with return code {returncode}. "
                "Please consult the kwallet-query man page for details"
            )
            return b""
        else:
            if stdout.lower().startswith(b"failed to read"):  # pyright: ignore
                print("failed to read password from kwallet. Using empty string instead")
                # this sometimes occurs in KDE because chrome does not check hasEntry and instead
                # just tries to read the value (which kwallet returns "") whereas kwallet-query
                # checks hasEntry. To verify this:
                # dbus-monitor "interface='org.kde.KWallet'" "type=method_return"
                # while starting chrome.
                # this was identified as a bug later and fixed in
                # https://chromium.googlesource.com/chromium/src/+/bbd54702284caca1f92d656fdcadf2ccca6f4165%5E%21/#F0
                # https://chromium.googlesource.com/chromium/src/+/5463af3c39d7f5b6d11db7fbd51e38cc1974d764
                return b""
            else:
                print("password found")
                return stdout.rstrip(b"\n")  # pyright: ignore
    except Exception as e:
        print(f"exception running kwallet-query: {e}")
        return b""


def _get_gnome_keyring_password(browser_keyring_name):
    try:
        import secretstorage  # pyright: ignore
    except ImportError:
        print("ERROR: Please install SecretStorage with `pip install SecretStorage`")
        sys.exit(-1)

    if not secretstorage:
        print("ERROR: Please install SecretStorage with `pip install SecretStorage`")
        sys.exit(-1)

    # the Gnome keyring does not seem to organise keys in the same way as KWallet,
    # using `dbus-monitor` during startup, it can be observed that chromium lists all keys
    # and presumably searches for its key in the list. It appears that we must do the same.
    # https://github.com/jaraco/keyring/issues/556
    with contextlib.closing(secretstorage.dbus_init()) as con:
        col = secretstorage.get_default_collection(con)
        for item in col.get_all_items():
            if item.get_label() == f"{browser_keyring_name} Safe Storage":
                return item.get_secret()
        print("failed to read from keyring")
        return b""


def _get_linux_keyring_password(browser_keyring_name, keyring):
    # note: chrome/chromium can be run with the following flags to determine which keyring backend
    # it has chosen to use
    # chromium --enable-logging=stderr --v=1 2>&1 | grep key_storage_
    # Chromium supports a flag: --password-store=<basic|gnome|kwallet> so the automatic detection
    # will not be sufficient in all cases.

    keyring = _LinuxKeyring[keyring] if keyring else _choose_linux_keyring()
    print(f"Chosen keyring: {keyring.name}")

    if keyring in (_LinuxKeyring.KWALLET, _LinuxKeyring.KWALLET5, _LinuxKeyring.KWALLET6):
        return _get_kwallet_password(browser_keyring_name, keyring)
    elif keyring == _LinuxKeyring.GNOMEKEYRING:
        return _get_gnome_keyring_password(browser_keyring_name)
    elif keyring == _LinuxKeyring.BASICTEXT:
        # when basic text is chosen, all cookies are stored as v10 (so no keyring password is required)
        return None
    assert False, f"Unknown keyring {keyring}"


def _get_mac_keyring_password(browser_keyring_name):
    print("using find-generic-password to obtain password from OSX keychain")
    try:
        stdout, _, returncode = Popen.run(
            [
                "security",
                "find-generic-password",
                "-w",  # write password to stdout
                "-a",
                browser_keyring_name,  # match 'account'
                "-s",
                f"{browser_keyring_name} Safe Storage",
            ],  # match 'service'
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
        )
        if returncode:
            print("find-generic-password failed")
            return None
        return stdout.rstrip(b"\n")  # pyright: ignore
    except Exception as e:
        print(f"exception running find-generic-password: {e}")
        return None


def _get_windows_v10_key(browser_root):
    """
    References:
        - [1] https://chromium.googlesource.com/chromium/src/+/refs/heads/main/components/os_crypt/sync/os_crypt_win.cc
    """
    path = _newest(_find_files(browser_root, "Local State"))
    if path is None:
        print("could not find local state file")
        return None
    print(f'Found local state file at "{path}"')
    with open(path, encoding="utf8") as f:
        data = json.load(f)
    try:
        # kOsCryptEncryptedKeyPrefName in [1]
        base64_key = data["os_crypt"]["encrypted_key"]
    except KeyError:
        print("no encrypted key in Local State")
        return None
    encrypted_key = base64.b64decode(base64_key)
    # kDPAPIKeyPrefix in [1]
    prefix = b"DPAPI"
    if not encrypted_key.startswith(prefix):
        print("invalid key")
        return None
    return _decrypt_windows_dpapi(encrypted_key[len(prefix) :])


def pbkdf2_sha1(password, salt, iterations, key_length):
    return hashlib.pbkdf2_hmac("sha1", password, salt, iterations, key_length)


def _decrypt_aes_cbc_multi(ciphertext, keys, initialization_vector=b" " * 16, hash_prefix=False):
    for key in keys:
        plaintext = unpad_pkcs7(aes_cbc_decrypt_bytes(ciphertext, key, initialization_vector))
        try:
            if hash_prefix:
                return plaintext[32:].decode()
            return plaintext.decode()
        except UnicodeDecodeError:
            pass
    print("failed to decrypt cookie (AES-CBC) because UTF-8 decoding failed. Possibly the key is wrong?")
    return None


def _decrypt_aes_gcm(ciphertext, key, nonce, authentication_tag, hash_prefix=False):
    try:
        plaintext = aes_gcm_decrypt_and_verify_bytes(ciphertext, key, authentication_tag, nonce)
    except ValueError:
        print("failed to decrypt cookie (AES-GCM) because the MAC check failed. Possibly the key is wrong?")
        return None

    try:
        if hash_prefix:
            return plaintext[32:].decode()
        return plaintext.decode()
    except UnicodeDecodeError:
        print("failed to decrypt cookie (AES-GCM) because UTF-8 decoding failed. Possibly the key is wrong?")
        return None


def _decrypt_windows_dpapi(ciphertext):
    """
    References:
        - https://docs.microsoft.com/en-us/windows/win32/api/dpapi/nf-dpapi-cryptunprotectdata
    """

    import ctypes
    import ctypes.wintypes

    class DATA_BLOB(ctypes.Structure):
        _fields_ = [("cbData", ctypes.wintypes.DWORD), ("pbData", ctypes.POINTER(ctypes.c_char))]

    buffer = ctypes.create_string_buffer(ciphertext)
    blob_in = DATA_BLOB(ctypes.sizeof(buffer), buffer)
    blob_out = DATA_BLOB()
    ret = ctypes.windll.crypt32.CryptUnprotectData(
        ctypes.byref(blob_in),  # pDataIn
        None,  # ppszDataDescr: human readable description of pDataIn
        None,  # pOptionalEntropy: salt?
        None,  # pvReserved: must be NULL
        None,  # pPromptStruct: information about prompts to display
        0,  # dwFlags
        ctypes.byref(blob_out),  # pDataOut
    )
    if not ret:
        message = "Failed to decrypt with DPAPI. See  https://github.com/yt-dlp/yt-dlp/issues/10927  for more info"
        print(f"ERROR: Download error: {message}")
        sys.exit(-1)

    result = ctypes.string_at(blob_out.pbData, blob_out.cbData)
    ctypes.windll.kernel32.LocalFree(blob_out.pbData)
    return result


def _config_home():
    return os.environ.get("XDG_CONFIG_HOME", os.path.expanduser("~/.config"))


def _open_database_copy(database_path, tmpdir):
    # cannot open sqlite databases if they are already in use (e.g. by the browser)
    database_copy_path = os.path.join(tmpdir, "temporary.sqlite")
    shutil.copy(database_path, database_copy_path)
    conn = sqlite3.connect(database_copy_path)
    return conn.cursor()


def _get_column_names(cursor, table_name):
    table_info = cursor.execute(f"PRAGMA table_info({table_name})").fetchall()
    return [row[1].decode() for row in table_info]


def _newest(files):
    return max(files, key=lambda path: os.lstat(path).st_mtime, default=None)


def _find_files(root, filename):
    # if there are multiple browser profiles, take the most recently used one
    i = 0
    for curr_root, _, files in os.walk(root):
        for file in files:
            i += 1
            if file == filename:
                yield os.path.join(curr_root, file)


def _is_path(value):
    return any(sep in value for sep in (os.path.sep, os.path.altsep) if sep)


# AES


def compat_ord(c):
    return c if isinstance(c, int) else ord(c)


def aes_cbc_decrypt_bytes(data, key, iv):
    """Decrypt bytes with AES-CBC using native implementation since pycryptodome is unavailable"""
    return bytes(aes_cbc_decrypt(*map(list, (data, key, iv))))


def aes_gcm_decrypt_and_verify_bytes(data, key, tag, nonce):
    """Decrypt bytes with AES-GCM using native implementation since pycryptodome is unavailable"""
    return bytes(aes_gcm_decrypt_and_verify(*map(list, (data, key, tag, nonce))))


def aes_cbc_encrypt_bytes(data, key, iv, **kwargs):
    return bytes(aes_cbc_encrypt(*map(list, (data, key, iv)), **kwargs))


BLOCK_SIZE_BYTES = 16


def unpad_pkcs7(data):
    return data[: -compat_ord(data[-1])]


def pkcs7_padding(data):
    """
    PKCS#7 padding

    @param {int[]} data        cleartext
    @returns {int[]}           padding data
    """

    remaining_length = BLOCK_SIZE_BYTES - len(data) % BLOCK_SIZE_BYTES
    return data + [remaining_length] * remaining_length


def pad_block(block, padding_mode):
    """
    Pad a block with the given padding mode
    @param {int[]} block        block to pad
    @param padding_mode         padding mode
    """
    padding_size = BLOCK_SIZE_BYTES - len(block)

    PADDING_BYTE = {
        "pkcs7": padding_size,
        "iso7816": 0x0,
        "whitespace": 0x20,
        "zero": 0x0,
    }

    if padding_size < 0:
        raise ValueError("Block size exceeded")
    elif padding_mode not in PADDING_BYTE:
        raise NotImplementedError(f"Padding mode {padding_mode} is not implemented")

    if padding_mode == "iso7816" and padding_size:
        block = [*block, 0x80]  # NB: += mutates list
        padding_size -= 1

    return block + [PADDING_BYTE[padding_mode]] * padding_size


def aes_ecb_encrypt(data, key, iv=None):
    """
    Encrypt with aes in ECB mode. Using PKCS#7 padding

    @param {int[]} data        cleartext
    @param {int[]} key         16/24/32-Byte cipher key
    @param {int[]} iv          Unused for this mode
    @returns {int[]}           encrypted data
    """
    expanded_key = key_expansion(key)
    block_count = ceil(len(data) / BLOCK_SIZE_BYTES)

    encrypted_data = []
    for i in range(block_count):
        block = data[i * BLOCK_SIZE_BYTES : (i + 1) * BLOCK_SIZE_BYTES]
        encrypted_data += aes_encrypt(pkcs7_padding(block), expanded_key)

    return encrypted_data


def aes_ecb_decrypt(data, key, iv=None):
    """
    Decrypt with aes in ECB mode

    @param {int[]} data        cleartext
    @param {int[]} key         16/24/32-Byte cipher key
    @param {int[]} iv          Unused for this mode
    @returns {int[]}           decrypted data
    """
    expanded_key = key_expansion(key)
    block_count = ceil(len(data) / BLOCK_SIZE_BYTES)

    encrypted_data = []
    for i in range(block_count):
        block = data[i * BLOCK_SIZE_BYTES : (i + 1) * BLOCK_SIZE_BYTES]
        encrypted_data += aes_decrypt(block, expanded_key)
    return encrypted_data[: len(data)]


def aes_ctr_decrypt(data, key, iv):
    """
    Decrypt with aes in counter mode

    @param {int[]} data        cipher
    @param {int[]} key         16/24/32-Byte cipher key
    @param {int[]} iv          16-Byte initialization vector
    @returns {int[]}           decrypted data
    """
    return aes_ctr_encrypt(data, key, iv)


def aes_ctr_encrypt(data, key, iv):
    """
    Encrypt with aes in counter mode

    @param {int[]} data        cleartext
    @param {int[]} key         16/24/32-Byte cipher key
    @param {int[]} iv          16-Byte initialization vector
    @returns {int[]}           encrypted data
    """
    expanded_key = key_expansion(key)
    block_count = ceil(len(data) / BLOCK_SIZE_BYTES)
    counter = iter_vector(iv)

    encrypted_data = []
    for i in range(block_count):
        counter_block = next(counter)
        block = data[i * BLOCK_SIZE_BYTES : (i + 1) * BLOCK_SIZE_BYTES]
        block += [0] * (BLOCK_SIZE_BYTES - len(block))

        cipher_counter_block = aes_encrypt(counter_block, expanded_key)
        encrypted_data += xor(block, cipher_counter_block)
    return encrypted_data[: len(data)]


def aes_cbc_decrypt(data, key, iv):
    """
    Decrypt with aes in CBC mode

    @param {int[]} data        cipher
    @param {int[]} key         16/24/32-Byte cipher key
    @param {int[]} iv          16-Byte IV
    @returns {int[]}           decrypted data
    """
    expanded_key = key_expansion(key)
    block_count = ceil(len(data) / BLOCK_SIZE_BYTES)

    decrypted_data = []
    previous_cipher_block = iv
    for i in range(block_count):
        block = data[i * BLOCK_SIZE_BYTES : (i + 1) * BLOCK_SIZE_BYTES]
        block += [0] * (BLOCK_SIZE_BYTES - len(block))

        decrypted_block = aes_decrypt(block, expanded_key)
        decrypted_data += xor(decrypted_block, previous_cipher_block)
        previous_cipher_block = block
    return decrypted_data[: len(data)]


def aes_cbc_encrypt(data, key, iv, *, padding_mode="pkcs7"):
    """
    Encrypt with aes in CBC mode

    @param {int[]} data        cleartext
    @param {int[]} key         16/24/32-Byte cipher key
    @param {int[]} iv          16-Byte IV
    @param padding_mode        Padding mode to use
    @returns {int[]}           encrypted data
    """
    expanded_key = key_expansion(key)
    block_count = ceil(len(data) / BLOCK_SIZE_BYTES)

    encrypted_data = []
    previous_cipher_block = iv
    for i in range(block_count):
        block = data[i * BLOCK_SIZE_BYTES : (i + 1) * BLOCK_SIZE_BYTES]
        block = pad_block(block, padding_mode)

        mixed_block = xor(block, previous_cipher_block)

        encrypted_block = aes_encrypt(mixed_block, expanded_key)
        encrypted_data += encrypted_block

        previous_cipher_block = encrypted_block

    return encrypted_data


def aes_gcm_decrypt_and_verify(data, key, tag, nonce):
    """
    Decrypt with aes in GBM mode and checks authenticity using tag

    @param {int[]} data        cipher
    @param {int[]} key         16-Byte cipher key
    @param {int[]} tag         authentication tag
    @param {int[]} nonce       IV (recommended 12-Byte)
    @returns {int[]}           decrypted data
    """

    # XXX: check aes, gcm param

    hash_subkey = aes_encrypt([0] * BLOCK_SIZE_BYTES, key_expansion(key))

    if len(nonce) == 12:
        j0 = [*nonce, 0, 0, 0, 1]
    else:
        fill = (BLOCK_SIZE_BYTES - (len(nonce) % BLOCK_SIZE_BYTES)) % BLOCK_SIZE_BYTES + 8
        ghash_in = nonce + [0] * fill + list((8 * len(nonce)).to_bytes(8, "big"))
        j0 = ghash(hash_subkey, ghash_in)

    # TODO: add nonce support to aes_ctr_decrypt

    # nonce_ctr = j0[:12]
    iv_ctr = inc(j0)

    decrypted_data = aes_ctr_decrypt(data, key, iv_ctr + [0] * (BLOCK_SIZE_BYTES - len(iv_ctr)))
    pad_len = (BLOCK_SIZE_BYTES - (len(data) % BLOCK_SIZE_BYTES)) % BLOCK_SIZE_BYTES
    s_tag = ghash(
        hash_subkey,
        data
        + [0] * pad_len  # pad
        + list(
            (0 * 8).to_bytes(8, "big") + ((len(data) * 8).to_bytes(8, "big"))  # length of associated data
        ),  # length of data
    )

    if tag != aes_ctr_encrypt(s_tag, key, j0):
        raise ValueError("Mismatching authentication tag")

    return decrypted_data


def aes_encrypt(data, expanded_key):
    """
    Encrypt one block with aes

    @param {int[]} data          16-Byte state
    @param {int[]} expanded_key  176/208/240-Byte expanded key
    @returns {int[]}             16-Byte cipher
    """
    rounds = len(expanded_key) // BLOCK_SIZE_BYTES - 1

    data = xor(data, expanded_key[:BLOCK_SIZE_BYTES])
    for i in range(1, rounds + 1):
        data = sub_bytes(data)
        data = shift_rows(data)
        if i != rounds:
            data = list(iter_mix_columns(data, MIX_COLUMN_MATRIX))
        data = xor(data, expanded_key[i * BLOCK_SIZE_BYTES : (i + 1) * BLOCK_SIZE_BYTES])

    return data


def aes_decrypt(data, expanded_key):
    """
    Decrypt one block with aes

    @param {int[]} data          16-Byte cipher
    @param {int[]} expanded_key  176/208/240-Byte expanded key
    @returns {int[]}             16-Byte state
    """
    rounds = len(expanded_key) // BLOCK_SIZE_BYTES - 1

    for i in range(rounds, 0, -1):
        data = xor(data, expanded_key[i * BLOCK_SIZE_BYTES : (i + 1) * BLOCK_SIZE_BYTES])
        if i != rounds:
            data = list(iter_mix_columns(data, MIX_COLUMN_MATRIX_INV))
        data = shift_rows_inv(data)
        data = sub_bytes_inv(data)
    return xor(data, expanded_key[:BLOCK_SIZE_BYTES])


def aes_decrypt_text(data, password, key_size_bytes):
    """
    Decrypt text
    - The first 8 Bytes of decoded 'data' are the 8 high Bytes of the counter
    - The cipher key is retrieved by encrypting the first 16 Byte of 'password'
      with the first 'key_size_bytes' Bytes from 'password' (if necessary filled with 0's)
    - Mode of operation is 'counter'

    @param {str} data                    Base64 encoded string
    @param {str,unicode} password        Password (will be encoded with utf-8)
    @param {int} key_size_bytes          Possible values: 16 for 128-Bit, 24 for 192-Bit or 32 for 256-Bit
    @returns {str}                       Decrypted data
    """
    NONCE_LENGTH_BYTES = 8

    data = list(base64.b64decode(data))
    password = list(password.encode())

    key = password[:key_size_bytes] + [0] * (key_size_bytes - len(password))
    key = aes_encrypt(key[:BLOCK_SIZE_BYTES], key_expansion(key)) * (key_size_bytes // BLOCK_SIZE_BYTES)

    nonce = data[:NONCE_LENGTH_BYTES]
    cipher = data[NONCE_LENGTH_BYTES:]

    decrypted_data = aes_ctr_decrypt(cipher, key, nonce + [0] * (BLOCK_SIZE_BYTES - NONCE_LENGTH_BYTES))
    return bytes(decrypted_data)


RCON = (0x8D, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36)
SBOX = (
    0x63,
    0x7C,
    0x77,
    0x7B,
    0xF2,
    0x6B,
    0x6F,
    0xC5,
    0x30,
    0x01,
    0x67,
    0x2B,
    0xFE,
    0xD7,
    0xAB,
    0x76,
    0xCA,
    0x82,
    0xC9,
    0x7D,
    0xFA,
    0x59,
    0x47,
    0xF0,
    0xAD,
    0xD4,
    0xA2,
    0xAF,
    0x9C,
    0xA4,
    0x72,
    0xC0,
    0xB7,
    0xFD,
    0x93,
    0x26,
    0x36,
    0x3F,
    0xF7,
    0xCC,
    0x34,
    0xA5,
    0xE5,
    0xF1,
    0x71,
    0xD8,
    0x31,
    0x15,
    0x04,
    0xC7,
    0x23,
    0xC3,
    0x18,
    0x96,
    0x05,
    0x9A,
    0x07,
    0x12,
    0x80,
    0xE2,
    0xEB,
    0x27,
    0xB2,
    0x75,
    0x09,
    0x83,
    0x2C,
    0x1A,
    0x1B,
    0x6E,
    0x5A,
    0xA0,
    0x52,
    0x3B,
    0xD6,
    0xB3,
    0x29,
    0xE3,
    0x2F,
    0x84,
    0x53,
    0xD1,
    0x00,
    0xED,
    0x20,
    0xFC,
    0xB1,
    0x5B,
    0x6A,
    0xCB,
    0xBE,
    0x39,
    0x4A,
    0x4C,
    0x58,
    0xCF,
    0xD0,
    0xEF,
    0xAA,
    0xFB,
    0x43,
    0x4D,
    0x33,
    0x85,
    0x45,
    0xF9,
    0x02,
    0x7F,
    0x50,
    0x3C,
    0x9F,
    0xA8,
    0x51,
    0xA3,
    0x40,
    0x8F,
    0x92,
    0x9D,
    0x38,
    0xF5,
    0xBC,
    0xB6,
    0xDA,
    0x21,
    0x10,
    0xFF,
    0xF3,
    0xD2,
    0xCD,
    0x0C,
    0x13,
    0xEC,
    0x5F,
    0x97,
    0x44,
    0x17,
    0xC4,
    0xA7,
    0x7E,
    0x3D,
    0x64,
    0x5D,
    0x19,
    0x73,
    0x60,
    0x81,
    0x4F,
    0xDC,
    0x22,
    0x2A,
    0x90,
    0x88,
    0x46,
    0xEE,
    0xB8,
    0x14,
    0xDE,
    0x5E,
    0x0B,
    0xDB,
    0xE0,
    0x32,
    0x3A,
    0x0A,
    0x49,
    0x06,
    0x24,
    0x5C,
    0xC2,
    0xD3,
    0xAC,
    0x62,
    0x91,
    0x95,
    0xE4,
    0x79,
    0xE7,
    0xC8,
    0x37,
    0x6D,
    0x8D,
    0xD5,
    0x4E,
    0xA9,
    0x6C,
    0x56,
    0xF4,
    0xEA,
    0x65,
    0x7A,
    0xAE,
    0x08,
    0xBA,
    0x78,
    0x25,
    0x2E,
    0x1C,
    0xA6,
    0xB4,
    0xC6,
    0xE8,
    0xDD,
    0x74,
    0x1F,
    0x4B,
    0xBD,
    0x8B,
    0x8A,
    0x70,
    0x3E,
    0xB5,
    0x66,
    0x48,
    0x03,
    0xF6,
    0x0E,
    0x61,
    0x35,
    0x57,
    0xB9,
    0x86,
    0xC1,
    0x1D,
    0x9E,
    0xE1,
    0xF8,
    0x98,
    0x11,
    0x69,
    0xD9,
    0x8E,
    0x94,
    0x9B,
    0x1E,
    0x87,
    0xE9,
    0xCE,
    0x55,
    0x28,
    0xDF,
    0x8C,
    0xA1,
    0x89,
    0x0D,
    0xBF,
    0xE6,
    0x42,
    0x68,
    0x41,
    0x99,
    0x2D,
    0x0F,
    0xB0,
    0x54,
    0xBB,
    0x16,
)
SBOX_INV = (
    0x52,
    0x09,
    0x6A,
    0xD5,
    0x30,
    0x36,
    0xA5,
    0x38,
    0xBF,
    0x40,
    0xA3,
    0x9E,
    0x81,
    0xF3,
    0xD7,
    0xFB,
    0x7C,
    0xE3,
    0x39,
    0x82,
    0x9B,
    0x2F,
    0xFF,
    0x87,
    0x34,
    0x8E,
    0x43,
    0x44,
    0xC4,
    0xDE,
    0xE9,
    0xCB,
    0x54,
    0x7B,
    0x94,
    0x32,
    0xA6,
    0xC2,
    0x23,
    0x3D,
    0xEE,
    0x4C,
    0x95,
    0x0B,
    0x42,
    0xFA,
    0xC3,
    0x4E,
    0x08,
    0x2E,
    0xA1,
    0x66,
    0x28,
    0xD9,
    0x24,
    0xB2,
    0x76,
    0x5B,
    0xA2,
    0x49,
    0x6D,
    0x8B,
    0xD1,
    0x25,
    0x72,
    0xF8,
    0xF6,
    0x64,
    0x86,
    0x68,
    0x98,
    0x16,
    0xD4,
    0xA4,
    0x5C,
    0xCC,
    0x5D,
    0x65,
    0xB6,
    0x92,
    0x6C,
    0x70,
    0x48,
    0x50,
    0xFD,
    0xED,
    0xB9,
    0xDA,
    0x5E,
    0x15,
    0x46,
    0x57,
    0xA7,
    0x8D,
    0x9D,
    0x84,
    0x90,
    0xD8,
    0xAB,
    0x00,
    0x8C,
    0xBC,
    0xD3,
    0x0A,
    0xF7,
    0xE4,
    0x58,
    0x05,
    0xB8,
    0xB3,
    0x45,
    0x06,
    0xD0,
    0x2C,
    0x1E,
    0x8F,
    0xCA,
    0x3F,
    0x0F,
    0x02,
    0xC1,
    0xAF,
    0xBD,
    0x03,
    0x01,
    0x13,
    0x8A,
    0x6B,
    0x3A,
    0x91,
    0x11,
    0x41,
    0x4F,
    0x67,
    0xDC,
    0xEA,
    0x97,
    0xF2,
    0xCF,
    0xCE,
    0xF0,
    0xB4,
    0xE6,
    0x73,
    0x96,
    0xAC,
    0x74,
    0x22,
    0xE7,
    0xAD,
    0x35,
    0x85,
    0xE2,
    0xF9,
    0x37,
    0xE8,
    0x1C,
    0x75,
    0xDF,
    0x6E,
    0x47,
    0xF1,
    0x1A,
    0x71,
    0x1D,
    0x29,
    0xC5,
    0x89,
    0x6F,
    0xB7,
    0x62,
    0x0E,
    0xAA,
    0x18,
    0xBE,
    0x1B,
    0xFC,
    0x56,
    0x3E,
    0x4B,
    0xC6,
    0xD2,
    0x79,
    0x20,
    0x9A,
    0xDB,
    0xC0,
    0xFE,
    0x78,
    0xCD,
    0x5A,
    0xF4,
    0x1F,
    0xDD,
    0xA8,
    0x33,
    0x88,
    0x07,
    0xC7,
    0x31,
    0xB1,
    0x12,
    0x10,
    0x59,
    0x27,
    0x80,
    0xEC,
    0x5F,
    0x60,
    0x51,
    0x7F,
    0xA9,
    0x19,
    0xB5,
    0x4A,
    0x0D,
    0x2D,
    0xE5,
    0x7A,
    0x9F,
    0x93,
    0xC9,
    0x9C,
    0xEF,
    0xA0,
    0xE0,
    0x3B,
    0x4D,
    0xAE,
    0x2A,
    0xF5,
    0xB0,
    0xC8,
    0xEB,
    0xBB,
    0x3C,
    0x83,
    0x53,
    0x99,
    0x61,
    0x17,
    0x2B,
    0x04,
    0x7E,
    0xBA,
    0x77,
    0xD6,
    0x26,
    0xE1,
    0x69,
    0x14,
    0x63,
    0x55,
    0x21,
    0x0C,
    0x7D,
)
MIX_COLUMN_MATRIX = ((0x2, 0x3, 0x1, 0x1), (0x1, 0x2, 0x3, 0x1), (0x1, 0x1, 0x2, 0x3), (0x3, 0x1, 0x1, 0x2))
MIX_COLUMN_MATRIX_INV = ((0xE, 0xB, 0xD, 0x9), (0x9, 0xE, 0xB, 0xD), (0xD, 0x9, 0xE, 0xB), (0xB, 0xD, 0x9, 0xE))
RIJNDAEL_EXP_TABLE = (
    0x01,
    0x03,
    0x05,
    0x0F,
    0x11,
    0x33,
    0x55,
    0xFF,
    0x1A,
    0x2E,
    0x72,
    0x96,
    0xA1,
    0xF8,
    0x13,
    0x35,
    0x5F,
    0xE1,
    0x38,
    0x48,
    0xD8,
    0x73,
    0x95,
    0xA4,
    0xF7,
    0x02,
    0x06,
    0x0A,
    0x1E,
    0x22,
    0x66,
    0xAA,
    0xE5,
    0x34,
    0x5C,
    0xE4,
    0x37,
    0x59,
    0xEB,
    0x26,
    0x6A,
    0xBE,
    0xD9,
    0x70,
    0x90,
    0xAB,
    0xE6,
    0x31,
    0x53,
    0xF5,
    0x04,
    0x0C,
    0x14,
    0x3C,
    0x44,
    0xCC,
    0x4F,
    0xD1,
    0x68,
    0xB8,
    0xD3,
    0x6E,
    0xB2,
    0xCD,
    0x4C,
    0xD4,
    0x67,
    0xA9,
    0xE0,
    0x3B,
    0x4D,
    0xD7,
    0x62,
    0xA6,
    0xF1,
    0x08,
    0x18,
    0x28,
    0x78,
    0x88,
    0x83,
    0x9E,
    0xB9,
    0xD0,
    0x6B,
    0xBD,
    0xDC,
    0x7F,
    0x81,
    0x98,
    0xB3,
    0xCE,
    0x49,
    0xDB,
    0x76,
    0x9A,
    0xB5,
    0xC4,
    0x57,
    0xF9,
    0x10,
    0x30,
    0x50,
    0xF0,
    0x0B,
    0x1D,
    0x27,
    0x69,
    0xBB,
    0xD6,
    0x61,
    0xA3,
    0xFE,
    0x19,
    0x2B,
    0x7D,
    0x87,
    0x92,
    0xAD,
    0xEC,
    0x2F,
    0x71,
    0x93,
    0xAE,
    0xE9,
    0x20,
    0x60,
    0xA0,
    0xFB,
    0x16,
    0x3A,
    0x4E,
    0xD2,
    0x6D,
    0xB7,
    0xC2,
    0x5D,
    0xE7,
    0x32,
    0x56,
    0xFA,
    0x15,
    0x3F,
    0x41,
    0xC3,
    0x5E,
    0xE2,
    0x3D,
    0x47,
    0xC9,
    0x40,
    0xC0,
    0x5B,
    0xED,
    0x2C,
    0x74,
    0x9C,
    0xBF,
    0xDA,
    0x75,
    0x9F,
    0xBA,
    0xD5,
    0x64,
    0xAC,
    0xEF,
    0x2A,
    0x7E,
    0x82,
    0x9D,
    0xBC,
    0xDF,
    0x7A,
    0x8E,
    0x89,
    0x80,
    0x9B,
    0xB6,
    0xC1,
    0x58,
    0xE8,
    0x23,
    0x65,
    0xAF,
    0xEA,
    0x25,
    0x6F,
    0xB1,
    0xC8,
    0x43,
    0xC5,
    0x54,
    0xFC,
    0x1F,
    0x21,
    0x63,
    0xA5,
    0xF4,
    0x07,
    0x09,
    0x1B,
    0x2D,
    0x77,
    0x99,
    0xB0,
    0xCB,
    0x46,
    0xCA,
    0x45,
    0xCF,
    0x4A,
    0xDE,
    0x79,
    0x8B,
    0x86,
    0x91,
    0xA8,
    0xE3,
    0x3E,
    0x42,
    0xC6,
    0x51,
    0xF3,
    0x0E,
    0x12,
    0x36,
    0x5A,
    0xEE,
    0x29,
    0x7B,
    0x8D,
    0x8C,
    0x8F,
    0x8A,
    0x85,
    0x94,
    0xA7,
    0xF2,
    0x0D,
    0x17,
    0x39,
    0x4B,
    0xDD,
    0x7C,
    0x84,
    0x97,
    0xA2,
    0xFD,
    0x1C,
    0x24,
    0x6C,
    0xB4,
    0xC7,
    0x52,
    0xF6,
    0x01,
)
RIJNDAEL_LOG_TABLE = (
    0x00,
    0x00,
    0x19,
    0x01,
    0x32,
    0x02,
    0x1A,
    0xC6,
    0x4B,
    0xC7,
    0x1B,
    0x68,
    0x33,
    0xEE,
    0xDF,
    0x03,
    0x64,
    0x04,
    0xE0,
    0x0E,
    0x34,
    0x8D,
    0x81,
    0xEF,
    0x4C,
    0x71,
    0x08,
    0xC8,
    0xF8,
    0x69,
    0x1C,
    0xC1,
    0x7D,
    0xC2,
    0x1D,
    0xB5,
    0xF9,
    0xB9,
    0x27,
    0x6A,
    0x4D,
    0xE4,
    0xA6,
    0x72,
    0x9A,
    0xC9,
    0x09,
    0x78,
    0x65,
    0x2F,
    0x8A,
    0x05,
    0x21,
    0x0F,
    0xE1,
    0x24,
    0x12,
    0xF0,
    0x82,
    0x45,
    0x35,
    0x93,
    0xDA,
    0x8E,
    0x96,
    0x8F,
    0xDB,
    0xBD,
    0x36,
    0xD0,
    0xCE,
    0x94,
    0x13,
    0x5C,
    0xD2,
    0xF1,
    0x40,
    0x46,
    0x83,
    0x38,
    0x66,
    0xDD,
    0xFD,
    0x30,
    0xBF,
    0x06,
    0x8B,
    0x62,
    0xB3,
    0x25,
    0xE2,
    0x98,
    0x22,
    0x88,
    0x91,
    0x10,
    0x7E,
    0x6E,
    0x48,
    0xC3,
    0xA3,
    0xB6,
    0x1E,
    0x42,
    0x3A,
    0x6B,
    0x28,
    0x54,
    0xFA,
    0x85,
    0x3D,
    0xBA,
    0x2B,
    0x79,
    0x0A,
    0x15,
    0x9B,
    0x9F,
    0x5E,
    0xCA,
    0x4E,
    0xD4,
    0xAC,
    0xE5,
    0xF3,
    0x73,
    0xA7,
    0x57,
    0xAF,
    0x58,
    0xA8,
    0x50,
    0xF4,
    0xEA,
    0xD6,
    0x74,
    0x4F,
    0xAE,
    0xE9,
    0xD5,
    0xE7,
    0xE6,
    0xAD,
    0xE8,
    0x2C,
    0xD7,
    0x75,
    0x7A,
    0xEB,
    0x16,
    0x0B,
    0xF5,
    0x59,
    0xCB,
    0x5F,
    0xB0,
    0x9C,
    0xA9,
    0x51,
    0xA0,
    0x7F,
    0x0C,
    0xF6,
    0x6F,
    0x17,
    0xC4,
    0x49,
    0xEC,
    0xD8,
    0x43,
    0x1F,
    0x2D,
    0xA4,
    0x76,
    0x7B,
    0xB7,
    0xCC,
    0xBB,
    0x3E,
    0x5A,
    0xFB,
    0x60,
    0xB1,
    0x86,
    0x3B,
    0x52,
    0xA1,
    0x6C,
    0xAA,
    0x55,
    0x29,
    0x9D,
    0x97,
    0xB2,
    0x87,
    0x90,
    0x61,
    0xBE,
    0xDC,
    0xFC,
    0xBC,
    0x95,
    0xCF,
    0xCD,
    0x37,
    0x3F,
    0x5B,
    0xD1,
    0x53,
    0x39,
    0x84,
    0x3C,
    0x41,
    0xA2,
    0x6D,
    0x47,
    0x14,
    0x2A,
    0x9E,
    0x5D,
    0x56,
    0xF2,
    0xD3,
    0xAB,
    0x44,
    0x11,
    0x92,
    0xD9,
    0x23,
    0x20,
    0x2E,
    0x89,
    0xB4,
    0x7C,
    0xB8,
    0x26,
    0x77,
    0x99,
    0xE3,
    0xA5,
    0x67,
    0x4A,
    0xED,
    0xDE,
    0xC5,
    0x31,
    0xFE,
    0x18,
    0x0D,
    0x63,
    0x8C,
    0x80,
    0xC0,
    0xF7,
    0x70,
    0x07,
)


def key_expansion(data):
    """
    Generate key schedule

    @param {int[]} data  16/24/32-Byte cipher key
    @returns {int[]}     176/208/240-Byte expanded key
    """
    data = data[:]  # copy
    rcon_iteration = 1
    key_size_bytes = len(data)
    expanded_key_size_bytes = (key_size_bytes // 4 + 7) * BLOCK_SIZE_BYTES

    while len(data) < expanded_key_size_bytes:
        temp = data[-4:]
        temp = key_schedule_core(temp, rcon_iteration)
        rcon_iteration += 1
        data += xor(temp, data[-key_size_bytes : 4 - key_size_bytes])

        for _ in range(3):
            temp = data[-4:]
            data += xor(temp, data[-key_size_bytes : 4 - key_size_bytes])

        if key_size_bytes == 32:
            temp = data[-4:]
            temp = sub_bytes(temp)
            data += xor(temp, data[-key_size_bytes : 4 - key_size_bytes])

        for _ in range(3 if key_size_bytes == 32 else 2 if key_size_bytes == 24 else 0):
            temp = data[-4:]
            data += xor(temp, data[-key_size_bytes : 4 - key_size_bytes])
    return data[:expanded_key_size_bytes]


def iter_vector(iv):
    while True:
        yield iv
        iv = inc(iv)


def sub_bytes(data):
    return [SBOX[x] for x in data]


def sub_bytes_inv(data):
    return [SBOX_INV[x] for x in data]


def rotate(data):
    return [*data[1:], data[0]]


def key_schedule_core(data, rcon_iteration):
    data = rotate(data)
    data = sub_bytes(data)
    data[0] = data[0] ^ RCON[rcon_iteration]

    return data


def xor(data1, data2):
    return [x ^ y for x, y in zip(data1, data2)]


def iter_mix_columns(data, matrix):
    for i in (0, 4, 8, 12):
        for row in matrix:
            mixed = 0
            for j in range(4):
                # xor is (+) and (-)
                mixed ^= (
                    0
                    if data[i : i + 4][j] == 0 or row[j] == 0
                    else RIJNDAEL_EXP_TABLE[(RIJNDAEL_LOG_TABLE[data[i + j]] + RIJNDAEL_LOG_TABLE[row[j]]) % 0xFF]
                )
            yield mixed


def shift_rows(data):
    return [data[((column + row) & 0b11) * 4 + row] for column in range(4) for row in range(4)]


def shift_rows_inv(data):
    return [data[((column - row) & 0b11) * 4 + row] for column in range(4) for row in range(4)]


def shift_block(data):
    data_shifted = []

    bit = 0
    for n in data:
        if bit:
            n |= 0x100
        bit = n & 1
        n >>= 1
        data_shifted.append(n)

    return data_shifted


def inc(data):
    data = data[:]  # copy
    for i in range(len(data) - 1, -1, -1):
        if data[i] == 255:
            data[i] = 0
        else:
            data[i] = data[i] + 1
            break
    return data


def block_product(block_x, block_y):
    # NIST SP 800-38D, Algorithm 1

    if len(block_x) != BLOCK_SIZE_BYTES or len(block_y) != BLOCK_SIZE_BYTES:
        raise ValueError(f"Length of blocks need to be {BLOCK_SIZE_BYTES} bytes")

    block_r = [0xE1] + [0] * (BLOCK_SIZE_BYTES - 1)
    block_v = block_y[:]
    block_z = [0] * BLOCK_SIZE_BYTES

    for i in block_x:
        for bit in range(7, -1, -1):
            if i & (1 << bit):
                block_z = xor(block_z, block_v)

            do_xor = block_v[-1] & 1
            block_v = shift_block(block_v)
            if do_xor:
                block_v = xor(block_v, block_r)

    return block_z


def ghash(subkey, data):
    # NIST SP 800-38D, Algorithm 2

    if len(data) % BLOCK_SIZE_BYTES:
        raise ValueError(f"Length of data should be {BLOCK_SIZE_BYTES} bytes")

    last_y = [0] * BLOCK_SIZE_BYTES
    for i in range(0, len(data), BLOCK_SIZE_BYTES):
        block = data[i : i + BLOCK_SIZE_BYTES]
        last_y = block_product(xor(last_y, block), subkey)

    return last_y


__all__ = [
    "aes_cbc_decrypt",
    "aes_cbc_decrypt_bytes",
    "aes_cbc_encrypt",
    "aes_cbc_encrypt_bytes",
    "aes_ctr_decrypt",
    "aes_ctr_encrypt",
    "aes_decrypt",
    "aes_decrypt_text",
    "aes_ecb_decrypt",
    "aes_ecb_encrypt",
    "aes_encrypt",
    "aes_gcm_decrypt_and_verify",
    "aes_gcm_decrypt_and_verify_bytes",
    "key_expansion",
    "pad_block",
    "pkcs7_padding",
    "unpad_pkcs7",
]

#########################################################################
# This is free and unencumbered software released into the public domain.

# Anyone is free to copy, modify, publish, use, compile, sell, or
# distribute this software, either in source code form or as a compiled
# binary, for any purpose, commercial or non-commercial, and by any
# means.

# In jurisdictions that recognize copyright laws, the author or authors
# of this software dedicate any and all copyright interest in the
# software to the public domain. We make this dedication for the benefit
# of the public at large and to the detriment of our heirs and
# successors. We intend this dedication to be an overt act of
# relinquishment in perpetuity of all present and future rights to this
# software under copyright law.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
# IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR
# OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
# ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
# OTHER DEALINGS IN THE SOFTWARE.

# For more information, please refer to <http://unlicense.org/>
#########################################################################

_HEADER = [
    "PRAGMA foreign_keys=OFF",
    "BEGIN TRANSACTION",
    (
        "CREATE TABLE moz_cookies (id INTEGER PRIMARY KEY, originAttributes TEXT NOT NULL DEFAULT '', name TEXT, "
        "value TEXT, host TEXT, path TEXT, expiry INTEGER, lastAccessed INTEGER, creationTime INTEGER, "
        "isSecure INTEGER, isHttpOnly INTEGER, inBrowserElement INTEGER DEFAULT 0, sameSite INTEGER DEFAULT 0, "
        "schemeMap INTEGER DEFAULT 0, isPartitionedAttributeSet INTEGER DEFAULT 0, "
        "CONSTRAINT moz_uniqueid UNIQUE (name, host, path, originAttributes))"
    ),
]


def parse_args() -> argparse.Namespace:
    """Parses cli arguments

    Returns:
        argparse.Namespace: parsed arguments
    """
    parser = argparse.ArgumentParser(
        description="Simple zero-dependency script that converts and decrypts cookies from chromium-based browser "
        "for importing into Mozilla's firefox-based browsers"
    )
    parser.add_argument(
        "browser",
        type=str,
        help=f"name of browser to extract cookies from (Available browsers: {','.join(CHROMIUM_BASED_BROWSERS)})",
        metavar="BROWSER_NAME",
    )
    parser.add_argument(
        "output",
        type=str,
        nargs="?",
        default="cookies.sqlite",
        help="where to save converted cookies (Default: cookies.sqlite)",
        metavar="OUTPUT_PATH",
    )
    parser.add_argument(
        "-p",
        "--profile",
        type=str,
        required=False,
        default=None,
        help="name/path of the profile to load cookies from (Default: auto)",
    )
    parser.add_argument(
        "-k",
        "--keyring",
        type=str,
        required=False,
        default=None,
        help="keyring name (Default: auto)",
    )
    parser.add_argument(
        "-a",
        "--append",
        type=str,
        required=False,
        default=None,
        help=(
            "append to existing database (cookies.sqlite) instead of creating a new one (only unique latest cookies "
            "(by lastAccessed) will be written to the output)"
        ),
        metavar="COOKIES_EXISTING_DATABASE_PATH",
    )
    parser.add_argument(
        "-o",
        "--overwrite",
        action="store_true",
        default=False,
        help="overwrite existing output database file",
    )
    return parser.parse_args()


def make_cookies_unique(cookies: list[dict[str, str | int]]) -> list[dict[str, str | int]]:
    """Makes cookies unique by keeping latest one (by lastAccessed time)

    Args:
        cookies (list[dict[str, str  |  int]]): non-unique cookies

    Returns:
        list[dict[str, str | int]]: unique cookies
    """
    cookies_unique: dict[tuple[str, str, str], dict[str, str | int]] = {}
    for cookie in cookies:
        key: tuple[str, str, str] = (
            str(cookie["name"]),
            str(cookie["host"]),
            str(cookie["path"]),
        )
        if key not in cookies_unique:
            cookies_unique[key] = cookie
        if int(cookie["lastAccessed"]) > int(cookies_unique[key]["lastAccessed"]):
            # print(
            #     f"Found more recent value for {cookie['host']}{cookie['path']}, {cookie['name']}: "
            #     f"{cookie['value']} @ {cookie['lastAccessed']} -> "
            #     f"{cookies_unique[key]['value']} @ {cookies_unique[key]['lastAccessed']} "
            # )
            cookies_unique[key] = cookie

    return list(cookies_unique.values())


def main() -> None:
    """Main entry"""
    # Parse CLI arguments
    args = parse_args()

    # Check browser
    if args.browser not in CHROMIUM_BASED_BROWSERS:
        print(f"ERROR: Unknown browser {args.browser}. Available browsers:  {','.join(CHROMIUM_BASED_BROWSERS)}")
        sys.exit(-1)

    # Check files
    if os.path.exists(args.output) and not args.overwrite:
        print(f"ERROR: Path {args.output} already exists! Specify -o / --overwrite to overwrite it")
        sys.exit(-1)
    if args.append and not os.path.exists(args.append):
        print(f"ERROR: Existing database path {args.append} doesn't exist")
        sys.exit(-1)

    cookies_parsed: list[dict[str, str | int]] = []

    # Parse existing database
    if args.append:
        with tempfile.TemporaryDirectory(prefix="chromium_to_mozilla_cookies") as tmpdir:
            cursor = _open_database_copy(args.append, tmpdir)
            cursor.execute(
                "SELECT id, originAttributes, name, value, host, path, expiry, lastAccessed, creationTime, "
                "isSecure, isHttpOnly, inBrowserElement, sameSite, schemeMap, "
                "isPartitionedAttributeSet FROM moz_cookies"
            )
            cookies_append_raw = cursor.fetchall()
        for cookie_append_raw in cookies_append_raw:
            if not cookie_append_raw:
                continue
            cookies_parsed.append(
                {
                    "originAttributes": cookie_append_raw[1],
                    "name": cookie_append_raw[2],
                    "value": cookie_append_raw[3],
                    "host": cookie_append_raw[4],
                    "path": cookie_append_raw[5],
                    "expiry": cookie_append_raw[6],
                    "lastAccessed": cookie_append_raw[7],
                    "creationTime": cookie_append_raw[8],
                    "isSecure": cookie_append_raw[9],
                    "isHttpOnly": cookie_append_raw[10],
                    "inBrowserElement": cookie_append_raw[11],
                    "sameSite": cookie_append_raw[12],
                    "schemeMap": cookie_append_raw[13],
                    "isPartitionedAttributeSet": cookie_append_raw[14],
                }
            )
        print(f"Extracted {len(cookies_parsed)} cookies from {args.append}")

    # Extract cookies from chromium
    cookies_raw = extract_chrome_cookies(args.browser, args.profile, args.keyring)
    if not cookies_raw:
        print("No cookies extracted")
        sys.exit(0)

    # Parse cookies
    for cookie_raw in cookies_raw:
        if not cookie_raw:
            continue
        (
            creation_utc,
            host_key,
            name,
            value,
            _,
            path,
            expires_utc,
            is_secure,
            is_httponly,
            last_access_utc,
            samesite,
            source_scheme,
        ) = cookie_raw

        if not host_key or not name:
            continue

        cookies_parsed.append(
            {
                "originAttributes": "",
                "name": name.decode("utf-8"),
                "value": value,
                "host": host_key.decode("utf-8"),
                "path": path.decode("utf-8"),
                "expiry": expires_utc // 1000000 - 11644473600,
                "lastAccessed": int((last_access_utc / 1000000 - 11644473600) * 1000 * 1000),
                "creationTime": int((creation_utc / 1000000 - 11644473600) * 1000 * 1000),
                "isSecure": is_secure,
                "isHttpOnly": is_httponly,
                "inBrowserElement": 0,
                "sameSite": samesite if samesite > 0 else 256,
                "schemeMap": source_scheme,
                "isPartitionedAttributeSet": 0,
            }
        )

    # Remove duplicates
    cookies = make_cookies_unique(cookies_parsed)

    # Write data
    conn = sqlite3.connect(args.output)
    cursor = conn.cursor()
    try:
        cursor.execute("DROP TABLE moz_cookies")
    except sqlite3.OperationalError:
        pass
    for header_sql in _HEADER:
        cursor.execute(header_sql)
    for i, cookie in enumerate(cookies):
        placeholders = "?"
        values: list[str | int] = [i + 1]
        for _, value in cookie.items():
            placeholders += ",?"
            values.append(value)
        try:
            cursor.execute(f"INSERT INTO moz_cookies VALUES({placeholders})", values)
        except sqlite3.OperationalError as e:
            print(f"WARNING: Unable to write cookie ({e}): {json.dumps(cookie, ensure_ascii=False)}")
    cursor.execute("COMMIT")
    conn.close()


if __name__ == "__main__":
    main()
