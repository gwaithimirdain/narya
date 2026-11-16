Source files must be valid UTF-8.  An invalid byte sequence is reported where the lexer reaches it, after the commands before it have been executed.

  $ printf 'axiom A : Type\necho A\naxiom x\200y : A\n' > lead.ny
  $ narya -v lead.ny
   ￫ info[I0001]
   ￮ axiom A assumed
  
  A
    : Type
  
   ￫ error[E0200]
   ￭ $TESTCASE_ROOT/lead.ny
   3 | axiom x�y : A
     ^ parse error: invalid UTF-8
  
  [1]

A multibyte sequence interrupted by another character is invalid, and the character after it is not swallowed.

  $ printf 'axiom A : Type\naxiom \342a : A\n' > interrupted.ny
  $ narya interrupted.ny
   ￫ error[E0200]
   ￭ $TESTCASE_ROOT/interrupted.ny
   2 | axiom �a : A
     ^ parse error: invalid UTF-8
  
  [1]

A sequence truncated by the end of the file:

  $ printf 'axiom A : Type\necho A \342\206' > truncated.ny
  $ narya truncated.ny
   ￫ error[E0200]
   ￭ $TESTCASE_ROOT/truncated.ny
   2 | echo A �
     ^ parse error: invalid UTF-8
  
  [1]

Overlong encodings and surrogates are invalid.

  $ printf 'axiom A : Type\naxiom\300\240B : Type\n' > overlong.ny
  $ narya overlong.ny
   ￫ error[E0200]
   ￭ $TESTCASE_ROOT/overlong.ny
   2 | axiom��B : Type
     ^ parse error: invalid UTF-8
  
  [1]

  $ printf 'axiom A : Type\naxiom s\355\240\200 : A\n' > surrogate.ny
  $ narya surrogate.ny
   ￫ error[E0200]
   ￭ $TESTCASE_ROOT/surrogate.ny
   2 | axiom s��� : A
     ^ parse error: invalid UTF-8
  
  [1]

Invalid UTF-8 is rejected even in comments and strings.

  $ printf 'axiom A : Type\n` a comment \377\n' > comment.ny
  $ narya comment.ny
   ￫ error[E0200]
   ￭ $TESTCASE_ROOT/comment.ny
   2 | ` a comment �
     ^ parse error: invalid UTF-8
  
  [1]

  $ printf 'axiom A : Type\n{` a block \377 comment `}\n' > block.ny
  $ narya block.ny
   ￫ error[E0200]
   ￭ $TESTCASE_ROOT/block.ny
   2 | {` a block � comment `}
     ^ parse error: invalid UTF-8
  
  [1]

  $ printf 'echo "a\377b"\n' > string.ny
  $ narya string.ny
   ￫ error[E0200]
   ￭ $TESTCASE_ROOT/string.ny
   1 | echo "a�b"
     ^ parse error: invalid UTF-8
  
  [1]

A valid character that cannot start a token, such as a Unicode tag character, is an error.

  $ printf 'axiom A : Type\necho A \363\240\201\201 A\n' > tag.ny
  $ narya tag.ny
   ￫ error[E0200]
   ￭ $TESTCASE_ROOT/tag.ny
   2 | echo A 󠁁 A
     ^ parse error: invalid character U+E0041
  
  [1]

C1 control characters are valid UTF-8, and survive reformatting.

  $ printf 'axiom z\302\205 : Type\n' > c1.ny
  $ narya c1.ny
  $ od -An -tx1 c1.ny
   61 78 69 6f 6d 20 7a c2 85 20 3a 20 54 79 70 65
   0a
