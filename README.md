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

5. Explore.