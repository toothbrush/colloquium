%include lhs2TeX.fmt
%include polycode.fmt
%include beamer.fmt
%include beamerboxed.fmt
%include specific.fmt
\newcommand{\nt}[1]{\note{\ensuremath{\circ} ~ ~ ~#1 \\ }}
\usetheme{Antibes}
\usecolortheme{whale}
\usefonttheme{structuresmallcapsserif}
% kill another warning:
\usepackage{textcomp}
\usepackage{verbatim}
\usepackage{graphicx}
\usepackage{latexsym}
\usepackage{amsfonts}
\usepackage{tikz}
\usepackage{dsfont}
\usepackage{listings}
\usepackage{xspace}
\newcommand{\ppause}{\pause \vspace{-3em}}
%colouring:
\definecolor{MyDarkGreen}{rgb}{0,0.5,0.45}
\newcommand{\comb}[1]{{\color{blue}\mathsf{#1}}}
\newcommand{\libfunc}[1]{{\color{MyDarkGreen}\mathsf{#1}}}
%end colouring

\setcounter{tocdepth}{1}
% get rid of LaTeX-beamer warning:
\let\Tiny=\tiny
% hm a bit ugly but ok:
\usepackage[T1]{fontenc}

\newcommand\unbound{{\rmfamily\scshape Unbound}\xspace}

\author{Paul van der Walt}
\institute{Utrecht University}
\date{15th December 2012}
\title[Binders Unbound]{Binders Unbound\\\small{by Weirich, Yorgey and Sheard}}
\begin{document}

\begin{frame}
    \maketitle
\end{frame}

\begin{frame}
    \tableofcontents
\end{frame}

\section{Introduction and Problem}
\begin{frame}{Problem}
    \begin{itemize}
        \item $\alpha$-equivalence and capture-avoiding substitution are conceptually simple
            \pause
            \nt{what is $\alpha$-equivalence? capture-avoiding substitution?}
        \item Implementation is a pain
        \item Subtle, boring \emph{boilerplate} code, prone to errors
        \item Maintenance hassle
    \end{itemize}
\end{frame}

\section{Solution}

\begin{frame}{Solution}
    \begin{itemize}
        \item Enter \unbound\cite{weirich2011binders}
        \item Out-of-the-box support for these problematic operations
        \item But, such tools already exist? (SYN\footnote{Scrap Your Nameplate, Cheney}, C$\alpha$ml\footnote{Pottier}, \ldots)
        \item These fall short
            \begin{itemize}
                \item Expressiveness
                \item Availability
                \item Choice of implementation
            \end{itemize}
    \end{itemize}

    \nt{certain binding patterns we'd like to specify can't be specified}
    \nt{availability: writing in your own language is preferable, but often this means having to update the tool each time the language changes. }
    \nt{swapping out (or writing own) implementations of binding specifications should be possible}
\end{frame}

\section{Introducing \unbound}
\begin{frame}{Concrete example}
    Representation of untyped lambda calculus
    \begin{example}
> type N   =    Name E
> data E   =    Var N
>          |    Lam (Bind N E)
>          |    App E E
    \end{example}
    \begin{itemize}
        \item $\comb{(library~type~combinators)}$
        \item |Name| represents variables, indexed by type % type here means expr / variable etc
        \item |Bind| represents a name paired with an expression (in which the name is bound)
    \end{itemize}
    \nt{Using concrete examples we'll motivate the available combinators}
    \nt{\unbound introduces type combinators which encode binding structure in the algebraic datatype itself}
    \nt{won't talk much about implementation and formal semantics of \unbound, more a tutorial}
\end{frame}
\begin{frame}{\unbound contribution}
    \begin{itemize}
        \item Compositional abstract combinators, small set
        \item Very expressive (examples to follow)\nt{supports many things like multiple atom types, pattern binders, recursive/nested binders \ldots}
        \item Formal semantics and correctness proof
        \item Haskell library for portability
    \end{itemize}
\end{frame}


\begin{frame}
From this, \unbound derives
    \begin{itemize}
        \item $\alpha$-equivalence
        \item free variable calculation
        \item capture-avoiding substitution
        \item \ldots
    \end{itemize}\nt{through Template Haskell and generic techniques}
\end{frame}

\begin{frame}{Parallel reduction: apply $\beta$- and $\eta$-reduction}
    \begin{spec}
red :: Fresh m => E -> m E
red (Var x) = return (Var x)
red (Lam b) = do
  (x,e) <- unbind b
  e'    <- red e
  case e' of -- eta-rule
      App e'' (Var y) | x == y && not (x `elem` fv e'') -> return e''
      _                -> return (Lam (bind x e'))
  \end{spec}
  \nt{$\eta: \lambda x . e x = e$}
  \nt{$\beta: (\lambda x . e) t = e [ x \mapsto t]$}
  \nt{avoiding capture! intuitively easy!}
  \end{frame}
  \begin{frame}{Continuing with the $App$-case}
      \begin{spec}
red (App e1 e2) = do
    e1p <- red e1
    case e1p of
        Lam b -> do -- beta-rule
            (x, e') <- unbind b
            e2p <- red e2
            return (subst x e2p e') -- capture-avoiding
        _ -> do
            e2p <- red e2
            return (App e1p e2p)
  \end{spec}
  $\libfunc{(derived~functions)}$

\end{frame}

\begin{frame}{The \unbound type combinators}
    $T \in \mathds{T}$
    \begin{description}
        \item[|Name T|] Names for Ts
        \item[|R|] Regular datatype containing only terms
        \item[|Bind P T|] Bind pattern P in body T
    \end{description}
    $P \in \mathds{P}$
    \begin{description}
        \item[|Name T|] Single binding name
        \item[$R_P$] Regular datatype containing only patterns
        \item[|Embed T|] Embedded term (to be discussed)
        \item[|Rebind P P|] Nested binding pattern
        \item[|Rec P|] Recursive binding pattern
    \end{description}
    \nt{\unbound uses 2 sorts of types:}
    \nt{terms: names are references to binding sites}
    \nt{patterns: names are binding occurences}
    \nt{regular = unit, base types, sums, products, lfp's}
    \nt{$\mathds{P}$ determines expressiveness: we'll explain Embed, Rebind, Rec later}
\end{frame}

\begin{frame}
    \begin{itemize}
        \item Key feature: no limitation to one binder at a time!
        \item $bind$ constructor takes a pattern, abstracts over all variables
        \item E.g. $\lambda x~y~z \to \ldots$ as sugar for $\lambda x \to \lambda y \to \lambda z \to \ldots$\footnote{With $x,y,z$ distinct.\nt{\unbound supports shadowing, but not in one pattern.}}
    \end{itemize}
> data E    =   Var N
>           |   Lam (Bind [N] E)
>           |   App E E
\nt{$Bind$ takes pattern type, term type, returns term type.}
Another example, adding |case| with pattern-matching:
\pause
\begin{spec}
data    Pat     =   PVar N | PCon String [Pat]
data    E       =   ...
                |   Con String [E]      -- data constructors
                |   Case E [Bind Pat E]   -- pattern matching
\end{spec}
\end{frame}

\begin{frame}{|let| binding}
    Introducing simple |let| bindings (|let x = e1 in e2|) is also easy.
    \begin{spec}
        data E  =   ...
                |   Let (Bind [(N, Embed E)] E)
    \end{spec}
    \begin{itemize}
        \item |Embed| may only occur in pattern types
        \item ``escape hatch'' for embedding terms which don't bind any names
        \nt{a term type within |Embed| may contain pattern types (inside lhs of |Bind|), which may again contain
        |Embed|ded term types.}
        \nt{Note that we have a list of pairs, this is to prevent nonsensical (mismatched) lengths}
    \end{itemize}
\end{frame}

\begin{frame}{Improvement: Nested binding using |Rebind|}
    Introducing the nested |let*|: \\
    |let* x1 = e1, ..., xn = en in e|
    \begin{spec}
type    N1  =   Name E
type    N2  =   Name E
Bind (Rebind N1 (N2, Embed E1)) E2
    \end{spec}
    \nt{|Rebind P1 P2| acts like the pattern type |(P1,P2)|, except that |P1| also scopes over |P2|}%
    \nt{Here, |N1| and |N2| are bound in |E2|, and additionally |N1| is also bound in |E1|.}%
    \pause
    Generalises to:
    \begin{spec}
data Lets   =   Nil
            |   Cons (Rebind (N, Embed E) Lets)
            \end{spec}
            \ppause
            \begin{spec}
data E      =   ...
            |   LetStar (Bind Lets E)
    \end{spec}
\end{frame}
\begin{frame}{This is cool because\ldots}
    \begin{itemize}
        \item |Rebind| allows support for \emph{telescopes}\footnote{A telescope $\Lambda$ is a sequence of variables with types: $x_1 : A_1, \ldots, x_n : A_n$.}
            \pause
        \item Allows encoding of dependently typed systems, for example
        \item Provides machinery for working with telescopes, such as calculation of binding variables, multiple substitution in terms, substitution through telescopes
        \item What about |letrec|?
            \pause
        \item Enter |Rec|, ``recursive'' version of |Rebind| \nt{given |Rec P|, names in the pattern P scope over all other terms embedded in P, and since |Rec P| is also a pattern, names in P also scope over anythings that binds |Rec P|.}
    \end{itemize}
    \begin{spec}
data E  =   ...
        |   Letrec (Bind (Rec [(N, Embed E)]) E)
    \end{spec}
    \nt{Can't be done with |Rebind| since this only gives a telescope. Thus the motivation for a new combinator.}
\end{frame}

\section{Semantics}

\begin{frame}{Semantics}
    \begin{itemize}
        \item We've seen examples motivating the semantics
        \item \ldots but no formal definition
        \item Will be vague here, focusing on the how-to
    \end{itemize}
\end{frame}

\begin{frame}{Representation}
    \begin{itemize}
        \item Locally nameless
        \item Old idea (70s)
        \item Bound variables represented by de Bruijn indices
        \item Free variables by atoms \nt{ atoms can be any countably infinite set with decidable equality, not just strings}
    \end{itemize}
\end{frame}

\begin{frame}{Names, indices, patterns}
    \begin{itemize}
        \item How to interpret |j@k|?
        \item |j| references a pattern
        \item |k| references a binder
        \item $\alpha$-equivalence $\Leftrightarrow$ structural equality!
    \end{itemize}
    \begin{example}
        |Bind (bx, by, bz) (Bind bq 1@2)|
    \end{example}\nt{so |1@2| refers to |bz| since we count from 0}
    \nt{|nth| and |find| exist for looking up name resp. index given pattern and number resp name.}
\end{frame}

\newcommand{\iss}{ ::=& }

\begin{frame}{Syntax}
    Syntax of atoms, indices, terms and patterns (for representing terms with binding structure)
    \begin{align*}
        \mathds{A} \iss \left\{ \textnormal{x,y,z},\cdots \right\}  \\
        b \iss\; j@@k  \\
        t \iss\; \textnormal{x}\; ||\; b\; ||\; \textnormal{K}~t_1 \ldots t_n\; ||\; \textnormal{Bind}~p~t  \\
        p \iss\; -_x\; ||\; \textnormal{K}~p_1 \ldots p_n  \; ||\; \textnormal{Rebind}~p~p\; ||\; \textnormal{Embed}~t \;||\; \textnormal{Rec}~p
    \end{align*}
    \nt{We separate terms and patterns}
    \nt{names in terms can be free or bound}
    \nt{K = constructor constants applied to 0\ldots $n$ subterms}
    \nt{K also handles generic/regular types}
    \nt{patterns can be constructors applied to subpatterns}
    \nt{$-_x$ are binders, emphasizing placeholder-ness}
\end{frame}



\begin{frame}{Open and close}
    \begin{itemize}
        \item |bind| and |unbind| are implemented in terms of:
            \pause
        \item |close| and |open|, important operations for locally nameless representation
    \end{itemize}
    \begin{block}{Helpers}
        \begin{spec}
            nth     ::  P -> dsN -> Maybe dsA
            find    ::  P -> dsA -> Maybe dsN
        \end{spec}
    \end{block}
    \nt{|close| replaces free variables which match a pattern-bound variable, with bound variables at the given level}
    \nt{|open| does the opposite, replaces bound variables (of the form |j@k|) with free variables referencing their binders in a pattern}
    \nt{|open| allows recursing under a binder}
    \nt{|nth| and |find| are useful for converting between numeric indices and names}
\end{frame}
\begin{frame}{Binding and unbinding}
\begin{itemize}
    \item Nothing special for binding
    \item Unbinding requires freshening
\end{itemize}
\begin{block}{Defs}
    \begin{spec}
bind      p t          = Bind p (close p t)
unbind    (Bind p t)   = (p', open p' t)
    where p' = freshen p
\end{spec}\nt{|freshen| is trivial; walks over structure and assigns fresh variable names, stopping at |Embed|}
\nt{since |Embed|s are not part of the pattern.}
\ppause
\begin{spec}
unrebind    (Rebind p1 p2)  =   (p1, openP p1 p2)
unrec       (Rec p)         =   openP p p
\end{spec}
\nt{|openP| looks through patterns to find |Embed| terms which can be opened}
\nt{note that we mustn't re-freshen rebound things. why?}
\nt{when opening a bind, we must freshen it's variables}
\nt{but when opening a nested binding, fresh names have already been chosen, and some correspondence may exist between the outer bind and the variables inside the Rebind. this mustn't be broken. }
%TODO: example.
\end{block}
\end{frame}

\section{Theorems}
\begin{frame}{Metatheory}
    \begin{itemize}
        \item It's good to prove the semantics make sense
        \item Most proofs are rather straight forward, here only a summary will be given\footnote{In the paper most proofs are left out too.}
        \item Extension of single-binder case locally nameless representations
    \end{itemize}
\end{frame}

\begin{frame}{Local closure (LC)}
    \begin{itemize}
        \item Not all terms are good representations
        \item Only \alert{locally closed} terms and patterns can be constructed
        \item i.e. no dangling bound variables (@0@@0@)
            \pause
        \item Theorem: Constructors and destructors preserve LC
        \item Theorem: Substitution preserves LC
        \item Theorem: Freshening preserves LC
    \end{itemize}
\end{frame}

\begin{frame}{$\alpha$-equivalence}
    \begin{itemize}
        \item Theorem: $-\approx-$ is an equivalence relation (\emph{refl}, \emph{sym}, \emph{trans})
        \item Theorem: |fv| respects $\alpha$-equivalence ($t_1\approx t_2 \Rightarrow fv~t_1 = fv~t_2$)
        \item Theorem: Substitution respects $\alpha$-equivalence\nt{given $\alpha$-equiv terms and substitutions, applying them yields $\alpha$-equiv terms}
    \end{itemize}
    
\end{frame}


\begin{frame}{Interaction $\alpha$-equivalence with |bind|}
    Two bindings are $\alpha$-equivalent if we can freshen two patterns to the same new result, and then show that their bodies are $\alpha$-equivalent under a consistent renaming.
    \begin{block}{Theorem 7}
        If |freshen p1 -> p, pi1| and |freshen p2 -> p, pi2|\\ and $\pi_1 \cdot t_1 \approx \pi_2 \cdot t_2$\\ then |bind p1 t1| $\approx$ |bind p2 t2|.
    \end{block}
    \nt{Here pi are permutations returned by freshen, and $\pi \cdot t$ is the application of a permutation to a term. }
    
\end{frame}


\begin{frame}
    \begin{block}{Theorem 8}
        | fv (bind p t) = fvP p `union` (fv t - binders p) |
    \end{block}
    \pause
    \begin{block}{Theorem 9}
        If $\left\{ x \right\} \cup $ |fv t| is disjoint from |binders p|,\\
        then |subst x t (bind p t') = bind (substP x t p) (subst x t t')|
    \end{block}
\end{frame}

\section{Implementation}

\begin{frame}{About the implementation}
    \begin{itemize}
        \item Some relevant classes
        \item Alpha, Subst, Fresh
        \item RTM
    \end{itemize}
    \begin{block}{Important classes}
        \begin{spec}
class Alpha a where
    aeq     :: Mode -> a -> a -> Bool
class Monad m => Fresh m where
    fresh   :: Name a -> m (Name a)
class Subst b a where
    isVar   :: a -> Maybe (SubstName a b)
\end{spec}
    \end{block}\nt{EG: 
    \begin{spec}
    instance Alpha SourcePos where
        aeq _ _ _ = True
\end{spec}}
\nt{mode = pattern or term, different from semantics, they're not differentiated syntactically}
\nt{default impl @FreshM@ exists, which just gives variables a number}
\nt{Subst example: see code}
    \pause
    \alert{Demo}
\end{frame}


\section{Discussion} % / related work -- very brief!
\begin{frame}{Discussion}
    \begin{itemize}
        \item Many approaches possible (nominal)\nt{locally nameless turns out to be simpler. nominal impl is being worked on.}
        \item In practise \unbound is effective
        \item Being used in {\rmfamily \scshape Trellys}\nt{experimental dependently-typed language, for type checking and evaluation}
        \item ``Just works'', but performance is an issue\nt{performance: generic functions, also in freshness monad some terms will be opened and closed for each binding level; expensive. on the other hand, $\alpha$-equiv is cheaper than a nominal impl.}
        \item Much related work, old idea (see references)
    \end{itemize}
\end{frame}
\begin{frame}{Future work}
    \begin{itemize}
        \item Support for global bindings (modules, objects)
        \item Any atom type (currently |String|)\nt{all that's necessary is dec. eq.}
        \item Static distinction between names and patterns \nt{limitation of RepLib. Allows creation of nonsensical terms such as using a pattern as a term: |Embed (Embed N)|}
        \item \unbound doesn't keep track of the scope of names once unbound \nt{names can escape their scope}
    \end{itemize}
\end{frame}

\section{Conclusion}


\begin{frame}{Conclusion}
    \begin{itemize}
        \item Expressive specification language
        \item Simple and practical to use
        \item Valuable tool for exploration of programming language design (compilers, interpreters, type checkers)
    \end{itemize}
    \bibliography{bu}{} %2nd parm is width
    \bibliographystyle{plain}
\end{frame}


\end{document}
