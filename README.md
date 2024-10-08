# Telomare
> A simple but robust virtual machine

<p float="left">
  <img src="https://github.com/Stand-in-Language/stand-in-language/actions/workflows/telomare-ci.yml/badge.svg" />
  <a href="https://gitter.im/stand-in-language/Lobby?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge"
     title="Join the chat at https://gitter.im/stand-in-language/Lobby">
    <img src="https://badges.gitter.im/stand-in-language/Lobby.svg" /> 
  </a>
</p>


A virtual machine with a simple grammar evolved from simply typed lambda calculus, that eventually will have powerful static checking and an optimizing backend.

## Warning
This project is in active development. Do expect bugs and general trouble, and please let us know if you run into any by creating a new issue if one does not already exist.

## Quick Start

1. Clone this repository and change directory to it:
   ```sh
   $ git clone https://github.com/Stand-In-Language/stand-in-language.git
   $ cd stand-in-language
   ```
2. [Install Nix](https://nixos.org/nix/download.html):
   ```sh
   $ curl https://nixos.org/nix/install | sh
   ```
3. Optional (reduces build time by using telomare's cache):
   ```sh
   # Install cachix with nix-env or adding `cachix` to your `/etc/nixos/configuration.nix`'s' `environment.systemPackages` if in NixOS.
   $ cachix use telomare
   ```
4. Enter a Nix shell. This will setup an environment where all external dependencies will be available (such as `cabal` for building):
   ```sh
   $ nix develop # or nix develop -c zsh
   ```
5. Build the project:
   ```sh
   $ cabal build # or nix build
   ```
6. Run the tictactoe example and start playing with a friend (or run your own telomare file):
   ```sh
   $ cabal run telomare -- tictactoe.tel # or nix run . -- tictactoe.tel
   ```
7. Profit!

## Telomare REPL
1. Run:
   ```sh
   $ cd <your/local/proyect/location>/telomare
   $ nix develop -c zsh
   $ cabal run telomare-repl -- --haskell # or nix run .#repl
   ```
2. Profit!
   
## Git Hooks

You can setup your git configuration to automatically format and look for lint suggestions. Just run:

``` sh
$ git config core.hooksPath hooks
```

## Contributing
If you'd like to contribute, please fork the repository and use a feature branch. Pull requests are warmly welcome.

## Links
1. [A Better Model of Computation](http://sfultong.blogspot.com/2016/12/a-better-model-of-computation.html?m=1) by Sfultong
2. [SIL: Explorations in non-Turing Completeness](http://sfultong.blogspot.com/2017/09/sil-explorations-in-non-turing.html?m=1) by Sfultong
3. [Deconstructing Lambdas, Closures and Application](http://sfultong.blogspot.com/2018/04/deconstructing-lambdas-closures-and.html?m=1) by Sfultong
4. [Join the community's chat](https://gitter.im/stand-in-language/Lobby)


## Licensing
The code in this project is licensed under the Apache License 2.0. For more information, please refer to the [LICENSE file](https://github.com/Stand-In-Language/stand-in-language/blob/master/LICENSE).
