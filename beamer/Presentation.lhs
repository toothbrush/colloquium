%include lhs2TeX.fmt
%include polycode.fmt
%include beamer.fmt
%include beamerboxed.fmt
%include greek.fmt
%include specific.fmt

\usetheme{Warsaw}
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

% get rid of LaTeX-beamer warning:
\let\Tiny=\tiny
% hm a bit ugly but ok:
\usepackage[T1]{fontenc}

\newcommand\unbound{Unbound\xspace}

\author{Paul van der Walt}
\institute{Utrecht University}
\date{15th December 2012}
\title[Binders Unbound]{Binders Unbound\\\small{by Weirich, Yorgey and Sheard}}
\begin{document}

\begin{frame}
    \maketitle
\end{frame}

%TODO: question-> talk about process of refining eg let* or just give final definition?

%% OUTLINE:
% intro / problem statement
% solution: unbound DSL
% introducing unbound
% feature: binding patterns
% semantics
% theorems
% implementation

% discussion

% related work
% (discussion?)
% conclusion / summary / contribution

\begin{frame}
    \tableofcontents
\end{frame}

\begin{frame}{Problem}
    \begin{itemize}
        \item $\alpha$-equivalence and capture-avoiding substitution are conceptually simple
        \item Implementation is a pain
        \item Subtle, boring \emph{boilerplate} code, prone to errors
        \item Maintenance hassle
    \end{itemize}
\end{frame}

\begin{frame}{Solution}
    \begin{itemize}
        \item Enter \unbound
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

\begin{frame}{Concrete example}
    Representation of untyped lambda calculus
    \begin{example}
> type N   =    Name E
> data E   =    Var N
>          |    Lam (Bind N E)
>          |    App E E
    \end{example}
    \begin{itemize}
        \item \emph{Name} represents variables, indexed by type % type here means expr / variable etc
        \item \emph{Bind} represents a name paired with an expression (in which the name is bound)
    \end{itemize}
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

\end{frame}


\begin{frame}
    hello\cite{weirich2011binders}
\end{frame}


\begin{frame}
    \bibliography{bu}{} %2nd parm is width
    \bibliographystyle{plain}
    
\end{frame}
\end{document}
