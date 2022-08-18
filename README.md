# parser
A general parser combinator library for (Vect n i) in Idris2.

Largely a version of contrib's Data.String.Parser, but generalised from String to general Vects.

# Installing
To use this library, simply add the following to your `pack.toml`:
```
[custom.all.parser]
type   = "github"
url    = "https://github.com/idris-bayes/parser"
commit = "latest:master"
ipkg   = "parser.ipkg"
```
You can then `import Parser` to your project.
