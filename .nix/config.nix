{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  attribute = "wasmcert";

  default-bundle = "9.2";

  # one bundle per GH actions file
  bundles."9.0" = {
    rocqPackages.rocq-core.override.version = "9.0";
    rocqPackages.coq.override.version = "9.0";
  };
  bundles."9.1" = {
    rocqPackages.rocq-core.override.version = "9.1";
    rocqPackages.coq.override.version = "9.1";
    # disable reverse dependency run, decided not to stay compatible
    rocqPackages.CertiRocq.job = false;
  };
  bundles."9.2" = {
    rocqPackages.rocq-core.override.version = "9.2";
    rocqPackages.coq.override.version = "9.2";
  };

#   bundles."9.3" = {
#     rocqPackages.rocq-core.override.version = "9.3";
#     rocqPackages.coq.override.version = "9.3";
#   };

  ## Cachix caches to use in CI
  ## Below we list some standard ones
  cachix.coq = { };
  cachix.math-comp = { };
  cachix.coq-community = { };

  ## If you have write access to one of these caches you can
  ## provide the auth token or signing key through a secret
  ## variable on GitHub. Then, you should give the variable
  ## name here. For instance, coq-community projects can use
  ## the following line instead of the one above:
  # cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";

  ## Note that here, CACHIX_AUTH_TOKEN and CACHIX_SIGNING_KEY
  ## are the names of secret variables. They are set in
  ## GitHub's web interface.
}
