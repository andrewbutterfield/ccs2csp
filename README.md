# ccs2csp

Haskell coding of CCS to CSP translation ideas being developed
by Gerard Ekembe Ngondi.

## Installation

### Prerequisites

You need to install `stack`.

See <https://docs.haskellstack.org/en/stable/README/>. You are strongly advised to follow their advice regarding the PATH environment variable at <https://docs.haskellstack.org/en/stable/install_and_upgrade/#path>.

### Installing

1. Clone this repository at a suitable location  
`git clone https:<url-path>.git`

2. Enter the working directory.

3. Give command `stack install` and wait. The first time you run this might take a while as it may install a local version of the Haskell compiler and required libraries. When it is done it will have installed a program called `ccs2csp`.


4. For now, the easiest thing to do is to load up the examples module in the GHC interpreter (`ghci`) and experiment in there. It needs to be invoked as follows:  
```
stack ghci src/Examples.lhs
``` 

5. The browse command `:browse` will list all defined objects with their types. Any object `obj :: CCS` can be translated (at least in principle). Entering the name of a CCS object at the interpreter prompt will show a pretty-printed version of it.

6. New objects can be created by editing `Examples.lhs` and giving the `:r` (reload) command from within GHCi.

7. A demo run of a translation can be run from within GHCi as follows, where `ccsObj` is the name of a CCS object:

```
ccs2csp "" ccsObj
```

8. To output to a file (`GEN.csp` say) simoply replace empty string by a filename:

```
ccs2csp "GEN.csp" ccsObj
```
The output is written to `GEN.csp` (here), with a summary printed out in the interpreter.