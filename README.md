# ccs2csp

Haskell coding of CCS to CSP translation ideas being developed
by Gerard Ekembe Ngondi.

## Acknowledgements

CCS parser derived from grammar file obtained from Aalborg
<https://github.com/caal/caal>.

See `OTHERS`

## Installation

### Prerequisites

You need to install `stack`.

See <https://docs.haskellstack.org/en/stable/README/>. You are strongly advised to follow their advice regarding the PATH environment variable at <https://docs.haskellstack.org/en/stable/install_and_upgrade/#path>.

### Installing

1. Clone this repository at a suitable location  
`git clone https:<url-path>.git`

2. Enter the working directory.

3. Give command `stack install` and wait. The first time you run this might take a while as it may install a local version of the Haskell compiler and required libraries. When it is done it will have installed a program called `ccs2csp`.

To regenerate the BNFC modules, you need to have BNFC installed (digitalgrammars.com) and execute the following:

```
cd src
bnfc -m CCS.bnfc
make
```

All generated files except `AbsCCS.hs`, `LexCCS.hs` and `ParCCS.hs` can be removed.

In general this should not be required as the latest versions of the above three are kept in the repo. It is only if you modify `CCS.bnfc` for some reason that you need to do the above steps.

### Using

Running `ccs2csp --help` will produce the following output:

```
usage: ccs2csp [-prc] [infile[.ext1]] [outfile[.ext2]]
-prc expects a single CCS process rather than a full CCS program
infile[.ext1] defaults to 'stdin'
outfile[.ext1] defaults to 'stdout'
ext1 defaults to 'proc'
ext2 defaults to 'csp'
```

For now, only `ccs2csp -prc ....` works as only single-process translation is supported.

So, for example, in the `test` sub-directory, running  
`ccs2csp -prc bisimA bisimA`  
will result in `bisimA.proc` being translated into `bisimA.csp`.

The command `ccs2csp -prc` acts as a filter accepting input on `stdin` and outputting to `stdout`.
