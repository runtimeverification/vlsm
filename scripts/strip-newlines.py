#!/usr/bin/env python
import sys
import os

sys.path.insert(0, './coq-tools')
from strip_newlines import strip_newlines

def main():
    try:
        max_consecutive_newlines = int(sys.argv[1])
    except ValueError:
        print("The argument must be a positive number!")
    dirName = './theories'
    for subdir, dirs, files in os.walk(dirName):
        for f in files:
            if f.endswith(".v"):
                with open (os.path.join(subdir, f), 'r+') as file:
                    content = file.read()
                    file.seek(0)
                    file.write(strip_newlines(content, max_consecutive_newlines))
                    file.truncate()

if __name__ == "__main__":
    main()
