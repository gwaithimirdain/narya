# The Narya ProofGeneral mode as a Nix Emacs package.  Build it with the
# callPackage of an Emacs package set, so that it matches your Emacs, e.g.
#
#   (pkgs.emacsPackagesFor pkgs.emacs).emacsWithPackages (epkgs: [
#     (epkgs.callPackage "${narya}/proofgeneral/package.nix" { })
#   ])
#
# where narya is the source of this repository (such as a flake input).
{ lib, melpaBuild, proof-general }:

melpaBuild {
  pname = "narya";
  version = "0.1";
  src = lib.fileset.toSource {
    root = ./.;
    fileset = lib.fileset.fileFilter (file: file.hasExt "el") ./.;
  };
  packageRequires = [ proof-general ];
  meta = {
    description = "ProofGeneral mode for the Narya proof assistant";
    homepage = "https://github.com/gwaithimirdain/narya";
    license = lib.licenses.gpl3Plus;
  };
}
