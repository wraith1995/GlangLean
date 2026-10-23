#!/usr/bin/env python3
"""Package a clean committed checkout reproducibly; does not publish or tag."""
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'artifacts')
    args = parser.parse_args()
    if git('status', '--porcelain', '--untracked-files=normal').strip():
        raise SystemExit('Commit or preserve pending changes before packaging.')
    commit = git('rev-parse', 'HEAD').decode().strip()
    name = 'glang-artifact-' + commit[:12]
    tar = git('archive', '--format=tar', '--prefix=' + name + '/', commit)
    args.output.mkdir(parents=True, exist_ok=True)
    target = args.output / (name + '.tar.gz')
    with target.open('wb') as raw:
        with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as zipped:
            zipped.write(tar)
    files = []
    with tarfile.open(fileobj=io.BytesIO(tar)) as archive:
        for member in archive.getmembers():
            if member.isfile():
                payload = archive.extractfile(member).read()
                files.append({'path': member.name, 'bytes': len(payload),
                              'sha256': hashlib.sha256(payload).hexdigest()})
    manifest = {'commit': commit, 'archive': target.name,
                'sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
                'files': files}
    (args.output / (name + '.manifest.json')).write_text(json.dumps(manifest, indent=2)+'\n')
    print(target)
    print('SHA-256: ' + manifest['sha256'])

if __name__ == '__main__':
    main()
