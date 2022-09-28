BEGIN {s = 0}

# If the current line is an one-line comment, print it.

/\(\*.*\*)$/ {
    print $0
}

# If the current line is the beginning of a multi-line non-coqdoc comment, go to state 2.

/^\s*\(\*[^*]/ && !/\*)$/ {
    s = 2
}

# State 3 works as a fail-safe state: if we cannot detect a pattern for the indentation of a comment-block, 
# this will be printed out just as initially.

!/^\s*\(\*\*/ && !/\*)$/ {
    if ($0 == "") {
        print $0
    } else if (s == 1) {
        match ($0, /^\s*/, b)
        newstart = b[0]
        if (newstart == "") s = 3
        else {
            if (start != "") {
                if (length(start) > length(newstart)) s = 3
            } else {
                start = newstart
            }
        }
        if (s != 3) {
            print commentStart substr ($0, length (start) + 1)
        } else print $0
    } else print $0
  }

# If the current line is the beginning of a comment and it's not the ending of one, go to state 1, and save 
# the indentation of the line. If the line contains just the "(**", or it's a header, print it as it is.
# Else, add a newline and the proper indentation.

/^\s*\(\*\*/ && !/\*)$/ {
    if (s == 0) {
        s = 1
        start = ""
        match ($0, /^\s*/, a)
        commentStart = a[0]
        if ($0 == commentStart "(**" || substr ($0, 0, length (commentStart) + 5) == commentStart "(** *") print $0
        else print commentStart "(**\n" commentStart substr($0, length (commentStart) + 5)
    }
}

# If the current line is the ending of a multi-line comment and it contains only the "*)", go back to state 0.

/^\s*\*)$/ && !/^\s*\(\*.*\*)$/ {
    s = 0
}

# If the current line is the ending of a multi-line comment and it contains also the content of the last line of the block,
# in case of a coqdoc comment, add a newline before "*)", and if it's a non-coqdoc comment, print the line as it is.
# Go back to state 0.

!/^\s*\*)$/ && /\*)$/ && !/^\s*\(\*.*\*)$/ {
    if (s == 1) {
        match ($0, /^\s*/, b)
        newstart = b[0]
        if (newstart == "") s = 3
        else {
            if (start != "") {
                if (length(start) > length(newstart)) s = 3
            } else {
                start = newstart
            }
        }
        if (s != 3) {
            print commentStart substr ($0, length (start) + 1, length($0) - length (start) - 2 ) "\n" commentStart "*)"
        } else {
            print substr ($0, 0, length($0) - 3) "\n" commentStart "*)"
        }
    }
    else if (s == 3) {
        print substr ($0, 0, length($0) - 3) "\n" commentStart "*)"
    }
    else if (s == 2){
        print $0
    }
    s = 0
}
