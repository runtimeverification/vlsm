#!/usr/bin/env python
import sys
import os

sys.path.insert(0, './coq-tools')
from strip_newlines import strip_newlines

def getListOfFiles(dirName):
    listOfFile = os.listdir(dirName)
    allFiles = list()
    for entry in listOfFile:
        fullPath = os.path.join(dirName, entry)
        if os.path.isdir(fullPath):
            allFiles = allFiles + getListOfFiles(fullPath)
        else:
            allFiles.append(fullPath)
    return allFiles  


def main():
    dirName = './theories/VLSM'
    listOfFiles = getListOfFiles(dirName)
    for f in listOfFiles:
        if f.endswith(".v"):
            with open (f, 'r') as file:
               content = file.read()
            with open (f, 'w') as file:
               file.write(strip_newlines(content, int(sys.argv[1])))


if __name__ == "__main__":
    main()
