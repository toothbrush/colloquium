%include lhs2TeX.fmt
%include polycode.fmt
%include beamer.fmt
%include beamerboxed.fmt
%include greek.fmt
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

%TODO: question-> talk about process of refining eg let* or just give final definition?


\begin{frame}
    \tableofcontents
\end{frame}

\section{Introduction and Problem}
\begin{frame}{Problem}
    \begin{itemize}
        \item $\alpha$-equivalence and capture-avoiding substitution are conceptually simple
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
                \item Expressiveness %TODO: rehash §1 here
                \item Availability
                \item Choice of implementation
            \end{itemize}
    \end{itemize}
\end{frame}

\begin{frame}{\unbound contribution}
    \begin{itemize}
        \item Compositional abstract combinators, small set
        \item Very expressive (examples to follow; supporting \ldots) %TODO enumerate supported things
        \item Formal semantics and correctness proof
        \item Haskell library for portability
    \end{itemize}
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
        \item $\comb{Library~type~combinators}$
        \item |Name| represents variables, indexed by type % type here means expr / variable etc
        \item |Bind| represents a name paired with an expression (in which the name is bound)
    \end{itemize}
    \nt{\unbound introduces type combinators which encode binding structure in the algebraic datatype itself}
    %TODO explain role of Name / Bind
\end{frame}

\begin{frame}
From this, \unbound derives
    \begin{itemize}
        \item $\alpha$-equivalence
        \item free variable calculation
        \item capture-avoiding substitution
        \item \ldots
    \end{itemize}
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

  \end{frame}
  \begin{frame}{Continuing with the $App$-case}
      \begin{spec}
red (App e1 e2) = do
    e1' <- red e1
    case e1' of
        Lam b -> do -- beta-rule
            (x, e') <- unbind b
            e2' <- red e2
            return (subst x e2' e')
        _ -> do
            e2' <- red e2
            return (App e1' e2')
  \end{spec}
  $\libfunc{Derived~functions}$

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
    \nt{patterns: names are binding occurences}
    \nt{terms: names are references to binding sites}
    \nt{regular = unit, base types, sums, products, lfp's}
    \nt{$\mathds{P}$ determines expressiveness: we'll explain Embed, Rebind, Rec later}
\end{frame}

\section{Feature: Binding patterns}

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
\begin{spec}
data    Pat     =   PVar N | PCon String [Pat]
data    E       =   ...
                |   Con String [E]      -- data constructors
                |   Case E [Bind P E]   -- pattern matching
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
        \item Used for embedding terms which don't bind any names
        \nt{a term type within |Embed| may contain pattern types (lhs of |Bind|), which may again contain
        |Embed|ded types.}
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
    Generalises to:
    \begin{spec}
data Lets   =   Nil
            |   Cons (Rebind (N, Embed E) Lets)
data E      =   ...
            |   LetStar (Bind Lets E)
    \end{spec}
\end{frame}
\begin{frame}
    \begin{itemize}
        \item Allows support for \emph{telescopes}\footnote{A telescope $\Lambda$ is a sequence of variables with types: $x_1 : A_1, \ldots, x_n : A_n$.}
    \end{itemize}
\end{frame}
\begin{frame}
    hello
\end{frame}

\section{Semantics}

\section{Theorems}


\section{Implementation}


\section{Discussion}
\section{Related work}
\section{Conclusion} % AND contribution




\begin{frame}
    \bibliography{bu}{} %2nd parm is width
    \bibliographystyle{plain}
    
\end{frame}
\end{document}
