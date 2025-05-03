# Build helpers for Agda2hs libraries

{
  pkgs,
  agda2hs-lib,
}:
let
  # Imports
  inherit (pkgs.lib)
    filter
    ;
  inherit (pkgs.lib.strings)
    concatMapStrings
    ;

  # Definitions
  completeArgs =
    {
      pname,
      meta,
      buildInputs ? [ ],
      everythingFile ? "./Everything.agda",
      includePaths ? [ ],
      libraryName ? pname,
      libraryFile ? "${libraryName}.agda-lib",
      buildPhase ? null,
      installPhase ? null,
      extraExtensions ? [ ],
      ...
    } :
    let
      withPackages = agda2hs-lib.withPackages;
      agda2hsWithArgs = withPackages (filter (p: p ? isAgda2HsDerivation) buildInputs);
      includePathArgs = concatMapStrings (path: "-i" + path + " ") (
        includePaths ++ [ (dirOf everythingFile) ]
      );
    in
    {
      isAgda2HsDerivation = true;

      buildInputs = buildInputs ++ [ agda2hsWithArgs ];

      buildPhase = 
        ''
        runHook preBuild
        agda2hs ${includePathArgs} ${everythingFile}
        rm ${everythingFile} "${everythingFile}i"
        runHook postBuild
        '';
    };
in
{
  mkDerivation = args:
    pkgs.agdaPackages.mkDerivation (args // completeArgs args);
}
