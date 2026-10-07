Import compiled files

  $ cat >one.ny <<EOF
  > axiom A : Type
  > EOF

  $ cat >two.ny <<EOF
  > import "one"
  > axiom a0 : A
  > EOF

  $ narya one.ny

  $ narya -v two.ny
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (compiled)
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  

Modified files are recompiled

  $ touch one.ny

  $ narya -v two.ny
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (source)
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  

Files are recompiled if the flags change

  $ narya -dtt -v two.ny
   ￫ warning[W2303]
   ￮ file '$TESTCASE_ROOT/one.ny' was compiled with incompatible flags -arity 2 -direction e,refl,Id,ap -internal, recompiling
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (source)
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  

  $ narya two.ny
   ￫ warning[W2303]
   ￮ file '$TESTCASE_ROOT/one.ny' was compiled with incompatible flags -parametric -arity 1 -direction d -external, recompiling
  

Requiring a file multiple times

  $ cat >three.ny <<EOF
  > import "one"
  > axiom a1 : A
  > EOF

  $ narya three.ny

  $ cat >four.ny <<EOF
  > import "one"
  > import "two"
  > import "three"
  > axiom a2 : Id A a0 a1
  > EOF

  $ narya -v four.ny
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (compiled)
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/two.ny (compiled)
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/three.ny (compiled)
  
   ￫ info[I0001]
   ￮ axiom a2 assumed
  

Files are recompiled if their dependencies need to be

  $ touch one.ny

  $ narya -v four.ny
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (source)
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/two.ny
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/two.ny (source)
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/three.ny
  
   ￫ info[I0001]
   ￮ axiom a1 assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/three.ny (source)
  
   ￫ info[I0001]
   ￮ axiom a2 assumed
  

A file is loaded from source if a file it imports has no compiled version at all: whether an
import is compiled and up to date is asked about that import, not about the file importing it.

  $ cat >five.ny <<EOF
  > import "two"
  > EOF

  $ narya five.ny

  $ rm one.nyo

  $ narya -v five.ny
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/two.ny
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (source)
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/two.ny (source)
  

Circular dependency

  $ cat >foo.ny <<EOF
  > import "bar"
  > EOF

  $ cat >bar.ny <<EOF
  > import "foo"
  > EOF

  $ narya foo.ny
   ￫ error[E2300]
   ￮ circular imports:
     $TESTCASE_ROOT/foo.ny
       imports $TESTCASE_ROOT/bar.ny
       imports $TESTCASE_ROOT/foo.ny
  
  [1]

Import is relative to the file's directory

  $ mkdir subdir

  $ cat >subdir/one.ny <<EOF
  > axiom A:Type
  > EOF

  $ cat >subdir/two.ny <<EOF
  > import "one"
  > axiom a : A
  > EOF

  $ narya subdir/one.ny

  $ narya subdir/two.ny

  $ narya -v -e 'import "subdir/two"'
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/subdir/one.ny (compiled)
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/subdir/two.ny (compiled)
  

A file isn't loaded twice even if referred to in different ways

  $ narya -v -e 'import "subdir/one"' -e 'import "subdir/two"'
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/subdir/one.ny (compiled)
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/subdir/two.ny (compiled)
  

Notations are used from explicitly imported files, but not transitively.

  $ cat >n1.ny <<EOF
  > axiom A:Type
  > axiom f : A -> A -> A
  > axiom a:A
  > EOF

  $ cat >n2.ny <<EOF
  > import "n1"
  > notation(0) x "&" y := f x y
  > EOF

  $ cat >n3.ny <<EOF
  > import "n1"
  > import "n2"
  > notation(0) x "%" y := f x y
  > EOF

  $ narya n1.ny

  $ narya n2.ny

  $ narya n1.ny n3.ny -e 'echo a % a'
   ￫ warning[E2209]
   ￮ replacing printing notation for f (previous notation will still be parseable)
  
  a % a
    : A
  

  $ narya n1.ny n3.ny -e 'echo a & a'
   ￫ warning[E2209]
   ￮ replacing printing notation for f (previous notation will still be parseable)
  
  a
    : A
  
   ￫ error[E0200]
   ￭ command-line exec string
   1 | echo a & a
     ^ parse error: invalid syntax
  
  [1]

Quitting in imports quits only that file

  $ cat >qone.ny <<EOF
  > axiom A : Type
  > quit
  > axiom B : Type
  > EOF

  $ narya qone.ny

  $ cat >qtwo.ny <<EOF
  > import "qone"
  > axiom a0 : A
  > EOF

  $ narya -v qtwo.ny
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/qone.ny (compiled)
  
   ￫ info[I0001]
   ￮ axiom a0 assumed
  
Dimensions work in files loaded from source

  $ cat >dim.ny <<EOF
  > axiom A:Type
  > axiom a0:A
  > axiom a1:A
  > axiom a2 : Id A a0 a1
  > EOF

  $ narya dim.ny

  $ narya -v -e 'import "dim" echo a2'
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/dim.ny (compiled)
  
  a2
    : Id A a0 a1
  
Echos are not re-executed in compiled files

  $ cat >echo.ny <<EOF
  > axiom A:Type
  > echo A
  > EOF

  $ narya -e 'import "echo"'
  A
    : Type
  

  $ narya -e 'import "echo"'
   ￫ warning[W2400]
   ￮ not re-executing echo/synth/show commands when loading compiled file $TESTCASE_ROOT/echo.nyo
  

A file loaded through a symlink has its compiled version next to the symlink, and is recompiled
when the symlink's target is modified

  $ mkdir symlib symproj

  $ cat >symlib/one.ny <<EOF
  > axiom A : Type
  > EOF

  $ ln -s ../symlib/one.ny symproj/one.ny

  $ cat >symproj/two.ny <<EOF
  > import "one"
  > axiom a : A
  > EOF

  $ narya symproj/two.ny

  $ test -e symproj/one.nyo && (test -e symlib/one.nyo || echo next to symlink)
  next to symlink

  $ touch -t 202001010000 symlib/one.ny symproj/one.nyo symproj/two.ny symproj/two.nyo

  $ touch -h -t 202001010000 symproj/one.ny

  $ cat >symlib/one.ny <<EOF
  > axiom A : Type
  > axiom B : Type
  > EOF

  $ narya -v symproj/two.ny
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/symproj/one.ny
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0001]
   ￮ axiom B assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/symproj/one.ny (source)
  
   ￫ info[I0001]
   ￮ axiom a assumed
  

The same file referred to with ".." is not loaded twice

  $ mkdir -p dots/sub

  $ cat >dots/d1.ny <<EOF
  > axiom A : Type
  > EOF

  $ narya -v -e 'import "dots/d1"' -e 'import "dots/sub/../d1"'
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/dots/d1.ny
  
   ￫ info[I0001]
   ￮ axiom A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/dots/d1.ny (source)
  

Nor if one of them is given on the command line

  $ narya -v dots/sub/../d1.ny -e 'import "dots/d1"'
   ￫ info[I0001]
   ￮ axiom A assumed
  
