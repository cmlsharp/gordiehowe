# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Walk an anonymous.4open.science repository's file listing (the listing API
# only) and write "sha<TAB>size<TAB>path" per file, sorted by path. Honors
# the API's rate limit (175 requests per 900 s).
#
#   python3 -I anon_list.py REPO_ID OUT.tsv
import json
import sys
import time
import urllib.error
import urllib.parse
import urllib.request

repo, manifest = sys.argv[1], sys.argv[2]
API = "https://anonymous.4open.science/api/repo/%s/files/" % repo


def get(path):
    url = API + ("?path=" + urllib.parse.quote(path) if path else "")
    for _ in range(20):
        req = urllib.request.Request(url, headers={"User-Agent": "curl/8.0"})
        try:
            with urllib.request.urlopen(req, timeout=60) as r:
                rem = int(r.headers.get("ratelimit-remaining", "100"))
                reset = int(r.headers.get("ratelimit-reset", "0"))
                body = r.read()
            if rem < 3:
                time.sleep(reset + 5)
            return json.loads(body)
        except urllib.error.HTTPError as e:
            reset = int(e.headers.get("ratelimit-reset", "60") or 60)
            print("HTTP", e.code, path, "sleep", reset + 5, file=sys.stderr, flush=True)
            time.sleep(min(reset + 5, 960))
        except Exception as e:
            print("err", path, e, file=sys.stderr, flush=True)
            time.sleep(10)
    raise SystemExit("failed " + path)


rows = []


def walk(path):
    for e in get(path):
        full = (path + "/" + e["name"]) if path else e["name"]
        if "sha" not in e and "size" not in e:
            walk(full)
        else:
            rows.append((e.get("sha"), e.get("size"), full))


walk("")
with open(manifest, "w") as m:
    for sha, size, full in sorted(rows, key=lambda r: r[2]):
        m.write("%s\t%s\t%s\n" % (sha, size, full))
print(len(rows), "files", file=sys.stderr)
