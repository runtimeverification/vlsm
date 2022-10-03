BEGIN {s = 0}

# We will reformat comments using a state-machine approach. 
# Initially, we are in state 0.
# If the current line is not the beginning of a comment or is the ending of a comment, print it.

!/^\s*\(\*\*/ || /\*)$/ {
    if (s == 0) print $0
}

# If the current line is not the ending of a comment, but a proper line inside a comment, print it.
# Else, if the comment block is already indented properly, go back to state 0 and print it as it is.
# If it's not the case, add the indentation.

!/^\s*\*)$/ { if (s == 1) {
    if ($0 == "") print $0
    else {
        if (commentIndent == "") {
        if (substr ($0, 0, 2 + length(commentStart)) == "  " commentStart) {
            s = 0
            commentIndent = ""
        }
        else commentIndent = "  " }
        print commentIndent $0 }
  }}

# If the current line is the ending of a comment, print it, update the commentIndent and go back to state 0.

/^\s*\*)$/ { if (s == 1) {
    commentIndent = ""
    s = 0
    print $0 }
}

# If the current line is the beginning of a comment and not the ending of one, print it, and, in case we are in
# state 0, go to state 1, and save the indentation of the starting comment in a variable.

/^\s*\(\*\*/ && !/\*)$/ {
    if (s == 0) {
        s = 1
        match ($0, /^\s*/, a)
        commentStart = a[0]
        commentIndent = ""
    }
    print $0
}
