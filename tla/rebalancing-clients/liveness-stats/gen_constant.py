#!/usr/bin/env python

import sys

count = int(sys.argv[1])
prefix = sys.argv[2]

for i in range(1, count+1):
    line = "{"
    for j in range(1, i+1):
        line = line + f"{prefix}{j}"
        if j < i:
            line = line + ","

    line = line + "}"

    if i < count:
        line = line + ","

    print(line)