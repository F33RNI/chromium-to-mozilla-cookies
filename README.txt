usage: python3 chromium-to-mozilla-cookies.py [-h] [-p PROFILE] [-k KEYRING] [-a COOKIES_EXISTING_DATABASE_PATH] [-o] BROWSER_NAME [OUTPUT_PATH]

Simple zero-dependency script that converts and decrypts cookies from chromium-based browser for importing into Mozilla's firefox-based
browsers

positional arguments:
  BROWSER_NAME          name of browser to extract cookies from (Available browsers: chromium,brave,whale,vivaldi,chrome,edge,opera)
  OUTPUT_PATH           where to save converted cookies (Default: cookies.sqlite)

options:
  -h, --help            show this help message and exit
  -p, --profile PROFILE
                        name/path of the profile to load cookies from (Default: auto)
  -k, --keyring KEYRING
                        keyring name (Default: auto)
  -a, --append COOKIES_EXISTING_DATABASE_PATH
                        append to existing database (cookies.sqlite) instead of creating a new one (only unique latest cookies (by
                        lastAccessed) will be written to the output)
  -o, --overwrite       overwrite existing output database file


example (brave -> librewolf):
    ./chromium-to-mozilla-cookies.py -o -a $HOME/.librewolf/redacted.default-default/cookies.sqlite brave
