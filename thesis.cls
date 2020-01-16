\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{thesis}

\LoadClass[12pt]{book}

\RequirePackage[margin=1in]{geometry}

\newcommand*{\supervisor}[1]{\gdef\@supervisor{#1}}

\makeatletter
\def\@maketitle{%
  \newpage
}
\makeatother
