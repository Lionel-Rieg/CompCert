# CompCert Install Instructions

## Dependencies

### Additional dependencies

Replace with the package manager for your distribution
```
sudo <pkg-manager> install -y mercurial darcs ocaml bubblewrap
```

### Opam

```
sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
```

## Post-install
Run
```
eval `opam config env`
```
Add this to your `.bashrc` or `.bash_profile`
```
. $HOME/.opam/opam-init/init.sh > /dev/null 2> /dev/null || true
```
Switch to a recent OCaml compiler version
```
opam switch create 4.09.0
opam switch 4.09.0
```
Install dependencies available through opam
```
opam install coq menhir
```

## Compilation
Pre-compilation configure replace the placeholder with your desired platform
(for Kalray Coolidge it is `kvx-cos`)
```
./configure <platform>
```
If using Kalray's platform, make sure that the kvx tools are on your path
Compile (adapt -j# to the number of cores and available RAM)
```
make -j12
make install
```

## Utilization
`ccomp` binaries are installed at `$(HOME)/.usr/bin`
Make sure to add that to your path to ease its use
Now you may use it like a regular compiler
```
ccomp -O3 test.c -S
ccomp -O3 test.c -o test.bin
```

## Changing platform
If you decide to change the platform, for instance from kvx-cos to kvx-mbr, you
should change the `compcert.ini` file with the respective tools and then run
```
make install
```

