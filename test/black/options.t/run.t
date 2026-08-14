The type theory in force is determined by the "option" commands at the beginning of a
source file, rather than by command-line flags.  A file specifies a *complete* set of
options: the absence of an "option parametric" command asserts higher observational type
theory just as positively as its presence asserts parametricity, and the absence of an
"option modal" command asserts the trivial mode theory.  All the sources loaded in a single
run must therefore agree.

A file declaring nothing gets the default theory.

  $ narya hott.ny
  refl a
    : Id A a a
  

A file declaring parametricity gets that instead.

  $ narya param.ny
  Br A
    : Type⁽ᵖ⁾ A A
  

Two files given on the command line must agree with each other.

  $ narya param.ny param2.ny
  Br A
    : Type⁽ᵖ⁾ A A
  

  $ narya param.ny hott.ny
  Br A
    : Type⁽ᵖ⁾ A A
  
   ￫ error[E2321]
   ￮ conflicting type theory options between file 'hott.ny' and
     the options already in force:
     theory (higher observational type theory vs. parametricity), direction letter (e vs. p), reflexivity names (refl,Id,ap vs. rel,Br)
  
  [1]

  $ narya hott.ny param.ny
  refl a
    : Id A a a
  
   ￫ error[E2321]
   ￮ conflicting type theory options between file 'param.ny' and
     the options already in force:
     theory (parametricity vs. higher observational type theory), direction letter (p vs. e), reflexivity names (rel,Br vs. refl,Id,ap)
  
  [1]

Setting the type theory on the command line is deprecated: the type theory is a property of
the code, so it belongs in the source.  The flags still work, and still specify only a
*partial* set of options -- they constrain what they mention and say nothing else -- so they
may agree with a file...

  $ narya -parametric param.ny
   ￫ warning[E0110]
   ￮ deprecated: setting the type theory on the command line (-parametric); use 'option' commands in the source file instead, or -e "option ..." when there is no file
  
  Br A
    : Type⁽ᵖ⁾ A A
  

...or conflict with it, including by conflicting with what the file's silence asserts.

  $ narya -parametric hott.ny
   ￫ warning[E0110]
   ￮ deprecated: setting the type theory on the command line (-parametric); use 'option' commands in the source file instead, or -e "option ..." when there is no file
  
   ￫ error[E2321]
   ￮ conflicting type theory options between file 'hott.ny' and
     the command line:
     theory (parametricity vs. higher observational type theory)
  
  [1]

  $ narya -arity 1 -direction d unary.ny
   ￫ warning[E0110]
   ￮ deprecated: setting the type theory on the command line (-arity -direction); use 'option' commands in the source file instead, or -e "option ..." when there is no file
  
  A⁽ᵈ⁾
    : Type⁽ᵈ⁾ A
  

  $ narya -arity 2 unary.ny
   ￫ warning[E0110]
   ￮ deprecated: setting the type theory on the command line (-arity); use 'option' commands in the source file instead, or -e "option ..." when there is no file
  
   ￫ error[E2321]
   ￮ conflicting type theory options between file 'unary.ny' and
     the command line: arity (2 vs. 1)
  
  [1]

An imported file must agree with the file importing it.

  $ rm -f *.nyo

  $ narya importer.ny
  Br A
    : Type⁽ᵖ⁾ A A
  
  A
    : Type
  

  $ narya badimporter.ny
   ￫ error[E2321]
   ￮ conflicting type theory options between file 'hott.ny' and
     the options already in force:
     theory (higher observational type theory vs. parametricity), direction letter (e vs. p), reflexivity names (refl,Id,ap vs. rel,Br)
  
  [1]

The whole set of options is validated at once, so the errors describe the configuration
rather than depending on the order the options were written in.

  $ narya needsparam.ny
   ￫ error[E2322]
   ￮ invalid type theory options:
     the discrete tconn mode theory requires 'option parametric', the discrete tconn mode theory requires arity 1
  
  [1]

An "option" command must come before any other command, since the type theory can't change
partway through a run.

  $ narya late.ny
   ￫ error[E2323]
   ￮ 'option' commands must come at the beginning of a file,
     before any other command: the type theory can't change partway through a
     run
  
  [1]

Two "option" commands in the same file must also agree.

  $ narya selfconflict.ny
   ￫ error[E2321]
   ￮ conflicting type theory options between file 'selfconflict.ny' and
     the options already in force: arity (2 vs. 1)
  
  [1]

Abbreviations expand to exactly the options they stand for.

  $ narya dttshort.ny
  A⁽ᵈ⁾
    : Type⁽ᵈ⁾ A
  

  $ narya dttlong.ny
  A⁽ᵈ⁾
    : Type⁽ᵈ⁾ A
  

The arity and the letter of a direction of parametricity are both required, with no
defaults: they are properties of the direction rather than of the theory as a whole.

  $ narya noarity.ny
   ￫ error[E2320]
   ￮ invalid 'option parametric': an 'arity' clause is required
  
  [1]

  $ narya noletter.ny
   ￫ error[E2320]
   ￮ invalid 'option parametric': a 'letter' clause is required
  
  [1]

Strings executed with -e are not complete artifacts, so like the command line they specify
only a partial set of options.  A run with no source file at all can therefore still set the
type theory, by putting an "option" command at the head of the string -- which is what the
deprecated flags should be replaced by.

  $ narya -parametric -e 'axiom A : Type echo Id A'
   ￫ warning[E0110]
   ￮ deprecated: setting the type theory on the command line (-parametric); use 'option' commands in the source file instead, or -e "option ..." when there is no file
  
  Id A
    : Type⁽ᵉ⁾ A A
  

  $ narya -e 'option parametric ≔ arity 2, letter p, name rel Br axiom A : Type echo Br A'
  Br A
    : Type⁽ᵖ⁾ A A
  
