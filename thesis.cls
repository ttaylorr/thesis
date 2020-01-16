\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{thesis}

\LoadClass[12pt]{book}

\RequirePackage[margin=1in]{geometry}
\RequirePackage[square,sort,comma,numbers]{natbib}
\RequirePackage{hyperref}

\newcommand*{\supervisor}[1]{\gdef\@supervisor{#1}}

\bibliographystyle{unsrt}

\makeatletter
\def\@maketitle{%
  \newpage
}
\makeatother
