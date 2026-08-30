{
  inputs = {
    naersk.url = "github:nix-community/naersk/master";
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, utils, naersk }:
    utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        naersk-lib = pkgs.callPackage naersk { };
      in
      {
        defaultPackage = naersk-lib.buildPackage ./.;
        devShell = with pkgs; mkShell {
          buildInputs = [
            cargo
            rustc
            rustfmt
            rust-analyzer
            pre-commit
            rustPackages.clippy

            # criterion picks this up at run time for `cargo bench` plots;
            # without it on PATH it prints "Gnuplot not found" and falls back
            # to the built-in plotters backend.
            gnuplot

            # PDF reading: text extraction + page/figure rendering
            poppler-utils # pdftotext, pdftoppm, pdfimages, pdfinfo
            mupdf         # mutool: structured text (JSON/HTML), draw
            imagemagick   # convert/magick: crop, upscale, montage figures
            ghostscript   # gs: rasterize/repair PDFs
          ];
          RUST_SRC_PATH = rustPlatform.rustLibSrc;
        };
      }
    );
}
