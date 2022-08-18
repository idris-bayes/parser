||| A simple parser combinator library for (Vect n i). Inspired by attoparsec zepto.
module Parser
import public Control.Monad.Identity
import Control.Monad.Trans

import Data.String
import Data.String.Extra
import Data.Fin
import Data.List
import Data.List.Alternating
import Data.List1
import Data.SnocList
import Data.Vect

%default total

||| The input state, pos is position in the string and maxPos is the length of the input string.
public export
record State i where
    constructor S
    maxLen : Nat
    input : Vect maxLen i
    pos : Nat

Show i => Show (State i) where
    show s = "(" ++ show s.input ++ ", " ++ show s.pos ++ ")"

||| Result of applying a parser
public export
data Result i a = Fail Nat String | OK a (State i)

Functor (Result i) where
    map f (Fail p err) = Fail p err
    map f (OK r s)     = OK (f r) s

public export
record ParseT (i : Type) (m : Type -> Type) (a : Type) where
    constructor P
    runParser : (Eq i, Show i) => State i -> m (Result i a)

public export
Parser : Type -> Type -> Type
Parser i = ParseT i Identity

public export
Functor m => Functor (ParseT i m) where
    map f p = P $ \s => map (map f) (p.runParser s)

public export
Monad m => Applicative (ParseT i m) where
    pure x = P $ \s => pure $ OK x s
    f <*> x = P $ \s => case !(f.runParser s) of
                            OK f' s' => map (map f') (x.runParser s')
                            Fail i err => pure $ Fail i err

public export
Monad m => Alternative (ParseT i m) where
    empty = P $ \s => pure $ Fail s.pos "no alternative left"
    a <|> b = P $ \s => case !(a.runParser s) of
                            OK r s' => pure $ OK r s'
                            Fail _ _ => b.runParser s

public export
Monad m => Monad (ParseT i m) where
    m >>= k = P $ \s => case !(m.runParser s) of
                             OK a s' => (k a).runParser s'
                             Fail i err => pure $ Fail i err

public export
MonadTrans (ParseT i) where
    lift x = P $ \s => map (flip OK s) x

||| Run a parser in a monad
||| Returns a tuple of the result and final position on success.
||| Returns an error message on failure.
export
parseT : {n : Nat} -> (Functor m, Eq i, Show i) => ParseT i m a -> Vect n i -> m (Either String (a, Nat))
parseT p is = map (\case
                       OK r s     => Right (r, s.pos)
                       Fail i err => Left $ "Parse failed at position [\{show i}/\{show $ length is}]: \{err}")
                   (p.runParser $ S n is 0)

||| Run a parser in a pure function
||| Returns a tuple of the result and final position on success.
||| Returns an error message on failure.
export
parse : {n : Nat} -> (Eq i, Show i) => Parser i a -> Vect n i -> Either String (a, Nat)
parse p is = runIdentity $ parseT p is

||| Gets the current input position. Useful for debugging.
export
getPos : Applicative m => ParseT i m Nat
getPos = P $ \s => pure $ OK (s.pos) s

||| Updates the position with a supplied updater function.
export
updatePos : Applicative m => (Nat -> Nat) -> ParseT i m ()
updatePos f = P $ \(S m inp p) => pure $ case f p > m || f p < 0 of
  True  => Fail p "tried to update position outside of input!"
  False => OK () $ S m inp (f p)

||| Combinator that replaces the error message on failure.
||| This allows combinators to output relevant errors
export
(<?>) : Functor m => ParseT i m a -> String -> ParseT i m a
(<?>) p msg = P $ \s => map (\case
                                OK r s'  => OK r s'
                                Fail i _ => Fail i msg)
                            (p.runParser s)

infixl 0 <?>

||| Combinator that combines the error message on failure with another.
||| This allows combinators to output relevant errors similar to a stack trace.
export
(<?+>) : Functor m => ParseT i m a -> String -> ParseT i m a
(<?+>) p m2 = P $ \s => map (\case
                                OK r s'   => OK r s'
                                Fail i m1 => Fail i $ m2 ++ ":\n\t" ++ m1)
                            (p.runParser s)
infixl 0 <?+>

||| Discards the result of a parser
export
skip : Functor m => ParseT i m a -> ParseT i m ()
skip = ignore

||| Maps the result of the parser `p` or returns `def` if it fails.
export
optionMap : Functor m => b -> (a -> b) -> ParseT i m a -> ParseT i m b
optionMap def f p = P $ \s => map (\case
                                     OK r s'  => OK (f r) s'
                                     Fail _ _ => OK def s)
                                  (p.runParser s)

||| Runs the result of the parser `p` or returns `def` if it fails.
export
option : Functor m => a -> ParseT i m a -> ParseT i m a
option def = optionMap def id

||| Returns a Bool indicating whether `p` succeeded
export
succeeds : Functor m => ParseT i m a -> ParseT i m Bool
succeeds = optionMap False (const True)

||| Returns a Maybe that contains the result of `p` if it succeeds or `Nothing` if it fails.
export
optional : Functor m => ParseT i m a -> ParseT i m (Maybe a)
optional = optionMap Nothing Just

||| Succeeds if and only if the argument parser fails.
|||
||| In Parsec, this combinator is called `notFollowedBy`.
export
requireFailure : Functor m => ParseT i m a -> ParseT i m ()
requireFailure (P runParser) = P $ \s => reverseResult s <$> runParser s
where
  reverseResult : State i -> Result i a -> Result i ()
  reverseResult s (Fail _ _) = OK () s
  reverseResult s (OK _ _)   = Fail (pos s) "purposefully changed OK to Fail"

||| Fail with some error message
export
fail : Applicative m => String -> ParseT i m a
fail x = P $ \s => pure $ Fail s.pos x

||| Succeeds if the next value satisfies the predicate `f`
export
satisfy : Applicative m => (i -> Bool) -> ParseT i m i
satisfy f = P $ \s => pure $ case natToFin s.pos s.maxLen of
                                 Just p => let idx = index p s.input in
                                               if f idx
                                                   then OK idx (S s.maxLen s.input $ s.pos + 1)
                                                   else Fail s.pos "could not satisfy predicate"
                                 Nothing => Fail s.pos "could not satisfy predicate"

||| Match a single input token
export
single : (Applicative m, Eq i, Show i) => i -> ParseT i m i
single x = satisfy (== x) <?> "expected \{show x}"

||| Parse and return a single input token.
export
anySingle : Applicative m => ParseT i m i
anySingle = satisfy (const True) <?> "reached end of string"

||| Parse and return a single input token, as long as it isn't x.
export
anySingleBut : (Applicative m, Eq i, Show i) => i -> ParseT i m i
anySingleBut x = satisfy (/= x) <?> "didn't expect \{show x}"

||| `satisfy`, but accepts a Char instead of an Int value.
export
satisfyChar : (Applicative m, Cast i Char) => (Char -> Bool) -> ParseT i m Char
satisfyChar f = map cast $ satisfy $ f . cast

||| Succeeds if the list of values `is` follows.
export
matchList : Applicative m => List i -> ParseT i m (List i)
matchList is = P $ \s => pure $ let len = length is in
                              if s.pos+len <= s.maxLen
                                  then let subv = drop s.pos is in
                                       if subv `isPrefixOf` is
                                         then OK is (S s.maxLen s.input (s.pos + len))
                                         else Fail s.pos ("expected \{show is}, got \{show subv}")
                                  else Fail s.pos ("reached end of input while searching for \{show is}")

||| Succeeds if the end of the input is reached.
export
eoi : Applicative m => ParseT i m ()
eoi = P $ \s => pure $ if s.pos == s.maxLen
                           then OK () s
                           else Fail s.pos "expected the end of the input"

||| Succeeds if the next char is `c`
export
char : (Applicative m, Cast i Char) => Char -> ParseT i m Char
char c = satisfyChar (== c) <?> "expected \{show c}"

||| Succeeds if the string `str` follows.
export
string : (Applicative m, Cast i Char, Cast Char i) => String -> ParseT i m String
string = map (fastPack . map cast) . matchList . map cast . fastUnpack

||| Parses a space character
export
space : (Applicative m, Cast i Char) => ParseT i m Char
space = satisfyChar isSpace <?> "expected space"

||| Parses a letter or digit (a character between \'0\' and \'9\').
||| Returns the parsed character.
export
alphaNum : (Applicative m, Cast i Char) => ParseT i m Char
alphaNum = satisfyChar isAlphaNum <?> "expected letter or digit"

||| Parses a letter (an upper case or lower case character). Returns the
||| parsed character.
export
letter : (Applicative m, Cast i Char) => ParseT i m Char
letter = satisfyChar isAlpha <?> "expected letter"

-- TODO: may be possible to make these total since we use vectors?
mutual
    ||| Succeeds if `p` succeeds, will continue to match `p` until it fails
    ||| and accumulate the results in a list
    export
    covering
    some : Monad m => ParseT i m a -> ParseT i m (List a)
    some p = [| p :: many p |]

    ||| Always succeeds, will accumulate the results of `p` in a list until it fails.
    export
    covering
    many : Monad m => ParseT i m a -> ParseT i m (List a)
    many p = some p <|> pure []

||| Parse left-nested lists of the form `((start op arg) op arg) op arg`
export
covering
hchainl : Monad m => ParseT i m start -> ParseT i m (start -> arg -> start) -> ParseT i m arg -> ParseT i m start
hchainl pst pop parg = pst >>= go
  where
  covering
  go : start -> ParseT i m start
  go x = (do op <- pop
             arg <- parg
             go $ op x arg) <|> pure x

||| Parse right-nested lists of the form `arg op (arg op (arg op end))`
export
covering
hchainr : Monad m => ParseT i m arg -> ParseT i m (arg -> end -> end) -> ParseT i m end -> ParseT i m end
hchainr parg pop pend = go id <*> pend
  where
  covering
  go : (end -> end) -> ParseT i m (end -> end)
  go f = (do arg <- parg
             op <- pop
             go $ f . op arg) <|> pure f

||| Always succeeds, applies the predicate `f` on chars until it fails and creates a string
||| from the results.
export
covering
takeWhile : Monad m => (i -> Bool) -> ParseT i m (List i)
takeWhile f = many (satisfy f)

||| Similar to `takeWhile` but fails if the resulting string is empty.
export
covering
takeWhile1 : Monad m => (i -> Bool) -> ParseT i m (List i)
takeWhile1 f = some (satisfy f)

||| Takes from the input until the `stop` pattern is found.
||| Fails if the `stop` pattern cannot be found.
export
covering
takeUntil : (Monad m, Eq i, Show i) => (stop : List i) -> ParseT i m (List i)
takeUntil stop = do
    case stop of
      []         => pure []
      (s :: top) => takeUntil' s top [<]
  where
    takeUntil' : Monad m' => (s : i) -> (top : List i) -> (acc : SnocList (List i)) -> ParseT i m' (List i)
    takeUntil' s top acc = do
        init <- takeWhile (/= s)
        skip $ single s <?> "end of string reached - \{show stop} not found"
        case !(succeeds $ matchList top) of
             False => takeUntil' s top $ acc :< (init `snoc` s)
             True  => pure $ concat $ acc :< init

||| Parses zero or more space characters
export
covering
spaces : (Monad m, Cast i Char) => ParseT i m ()
spaces = skip (many space)

||| Parses one or more space characters
export
covering
spaces1 : (Monad m, Cast i Char) => ParseT i m ()
spaces1 = skip (some space) <?> "whitespaces"

||| Discards brackets around a matching parser
export
parens : (Monad m, Cast i Char) => ParseT i m a -> ParseT i m a
parens p = char '(' *> p <* char ')'

||| Discards whitespace after a matching parser
export
covering
lexeme : (Monad m, Cast i Char) => ParseT i m a -> ParseT i m a
lexeme p = p <* spaces

||| Matches a specific string, then skips following whitespace
export
covering
token : (Monad m, Cast i Char, Cast Char i) => String -> ParseT i m ()
token s = lexeme (skip $ string s) <?> "expected token " ++ show s

||| Parse repeated instances of at least one `p`, separated by `s`,
||| returning a list of successes.
|||
||| @ p the parser for items
||| @ s the parser for separators
export
covering
sepBy1 : Monad m => (p : ParseT i m a)
                 -> (s : ParseT i m b)
                 -> ParseT i m (List1 a)
sepBy1 p s = [| p ::: many (s *> p) |]

||| Parse zero or more `p`s, separated by `s`s, returning a list of
||| successes.
|||
||| @ p the parser for items
||| @ s the parser for separators
export
covering
sepBy : Monad m => (p : ParseT i m a)
                -> (s : ParseT i m b)
                -> ParseT i m (List a)
sepBy p s = optionMap [] forget (p `sepBy1` s)

||| Parses /one/ or more occurrences of `p` separated by `comma`.
export
covering
commaSep1 : (Monad m, Cast i Char) => ParseT i m a -> ParseT i m (List1 a)
commaSep1 p = p `sepBy1` (char ',')

||| Parses /zero/ or more occurrences of `p` separated by `comma`.
export
covering
commaSep : (Monad m, Cast i Char) => ParseT i m a -> ParseT i m (List a)
commaSep p = p `sepBy` (char ',')

||| Parses alternating occurrences of `a`s and `b`s.
||| Can be thought of as parsing:
||| - a list of `b`s, separated, and surrounded, by `a`s
||| - a non-empty list of `a`s, separated by `b`s
||| where we care about the separators
export
covering
alternating : Monad m
           => ParseT i m a
           -> ParseT i m b
           -> ParseT i m (Odd a b)
alternating x y = do vx <- x
                     (vx ::) <$> [| y :: alternating x y |] <|> pure [vx]

||| Run the specified parser precisely `n` times, returning a vector
||| of successes.
export
ntimes : Monad m => (n : Nat) -> ParseT i m a -> ParseT i m (Vect n a)
ntimes    Z  p = pure Vect.Nil
ntimes (S n) p = [| p :: (ntimes n p) |]

||| Take `n` values from the input, returning a vector.
export
take : Monad m => (n : Nat) -> ParseT i m (Vect n i)
take n = ntimes n anySingle <?> "unexpected end of string"
