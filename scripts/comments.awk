BEGIN {s = 0}

# We will reformat comments using a state-machine approach.
# Initially, we are in state 0.
# If the current line is not the beginning of a comment, just print it and loop in the current state

!/^\s*\(\*\*$/ {
    if (s == 0) print $0
}

#If the current line is the beginning of a comment, move to state 1, and save the current line

/^\s*\(\*\*$/ {
    if (s == 0) {
        s = 1
        commentStart = $0
    }
}

# If the current line is the end of an one-line comment, trim the comment-line, join the comment on
# a single line and move back to the initial state 0.

/^\s*\*)$/ {
    if (s == 2) {
        sub(/^[ \t\r\n]+/, "", line)
        print commentStart " " line " *)"
    }
    s = 0 
}

!/^\s*\*)$/ && !/^\s*\(\*\*$/ {
    if (s == 1) { # Save the first line of the comment and move to state 2
        line = $0
        s = 2
    } else if (s == 2) { # In case of a multi-line comment, print its content unchanged, moving back to state 0
        print commentStart
        print line
        print $0
        s = 0
    }
}
