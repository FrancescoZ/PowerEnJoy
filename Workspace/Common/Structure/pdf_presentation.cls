% Copyright 2004 by Till Tantau <tantau@users.sourceforge.net>.
%
% In principle, this file can be redistributed and/or modified under
% the terms of the GNU Public License, version 2.
%
% However, this file is supposed to be a template to be modified
% for your own needs. For this reason, if you use this file as a
% template and not specifically distribute it as part of a another
% package/program, I grant the extra permission to freely copy and
% modify this file as you see fit and even to delete this copyright
% notice.
%
\ProvidesClass{pdf_presentation}
%
\LoadClass{beamer}

\usepackage{listings}
\usepackage{color}
\usepackage{graphicx}
\usepackage{caption}
\usepackage{array}
\usepackage{tabulary}
%
\definecolor{dkgreen}{rgb}{0,0.6,0}
\definecolor{gray}{rgb}{0.5,0.5,0.5}
\definecolor{mauve}{rgb}{0.58,0,0.82}
%
\newcolumntype{X}[1]{>{\raggedright\let\newline\\\arraybackslash\hspace{0pt}}m{#1}}	\newcolumntype{Y}[1]{>{\centering\let\newline\\\arraybackslash\hspace{0pt}}m{#1}}
\newcolumntype{Z}[1]{>{\raggedleft\let\newline\\\arraybackslash\hspace{0pt}}m{#1}}
%

%\usetheme{AnnArbor}
%\usetheme{Antibes}
%\usetheme{Bergen}
%\usetheme{Berkeley}
%\usetheme{Berlin}
%\usetheme{Boadilla}
%\usetheme{boxes}
%\usetheme{CambridgeUS}
%\usetheme{Copenhagen}
%\usetheme{Darmstadt}
%\usetheme{default}
%\usetheme{Frankfurt}
%\usetheme{Goettingen}
\usetheme{Hannover}
%\usetheme{Ilmenau}
%\usetheme{JuanLesPins}
%\usetheme{Luebeck}
%\usetheme{Madrid}
%\usetheme{Malmoe}
%\usetheme{Marburg}
%\usetheme{Montpellier}
%\usetheme{PaloAlto}
%\usetheme{Pittsburgh}
%\usetheme{Rochester}
%\usetheme{Singapore}
%\usetheme{Szeged}
%\usetheme{Warsaw}

\addtobeamertemplate{navigation symbols}{}{%
    \usebeamerfont{footline}%
    \usebeamercolor[fg]{footline}%
    \hspace{1em}%
    \insertframenumber/\inserttotalframenumber
}

\newcommand{\configureJava}{
	\lstset{%
		language=Java,
		aboveskip=3mm,
		belowskip=3mm,
		showstringspaces=false,
		columns=flexible,
		basicstyle={\small\ttfamily},
		numbers=none,
		numberstyle=\tiny\color{gray},
		keywordstyle=\color{blue},
		commentstyle=\color{dkgreen},
		stringstyle=\color{mauve},
		breaklines=true,
		breakatwhitespace=true,
		tabsize=3
	}
}
\newcommand{\enableCodeLineNumbers}{\lstset{numbers=left}}
\newcommand{\disableCodeLineNumbers}{\lstset{numbers=none}}

\subtitle{Software Engineering 2 Project}
%
\author{M.~Redaelli \and F.~Zanoli}


\institute[PoliMi]
{Politecnico di Milano}

\date{\today}


\pgfdeclareimage[height=0.75cm]{university-logo}{../Common/Resources/PoliLogo.png}
\logo{\pgfuseimage{university-logo}}

\AtBeginSection[]
{
	\begin{frame}<beamer>
		\frametitle{Outline - \insertsection}
		\tableofcontents[currentsection]
	\end{frame}
}
%
\newcommand{\titleToc}{%
		\begin{frame}
			\titlepage
		\end{frame}
		\begin{frame}{Outline}
			\tableofcontents
			% You might wish to add the option [pausesections]
		\end{frame}
}
%
\newcommand{\PowerEnJoy}[0]{\mbox{\emph{PowerEnJoy}}}
%
\newcommand{\unbreakableBlock}[1]{%
	\begin{minipage}{\linewidth}% Following stays together
		#1
	\end{minipage}
}
\newcommand{\centeredBlock}[1]{
	\begin{center}
		#1
	\end{center}
}
\newcommand{\unbreakableCenteredBlock}[1]{\unbreakableBlock{\centeredBlock{#1}}}
\newcommand{\unbreakableCenteredBlockSpaced}[1]{%
	\unbreakableCenteredBlock{%
		\vspace{0.5em}
		#1
		\vspace{0.5em}
	}
}
\newcommand{\unbreakableItem}[1]{\unbreakableBlock{\item #1}}
\newcommand{\showPercentImageNoCaption}[2]{%
	\unbreakableCenteredBlockSpaced{%
		\includegraphics[width=#2\textwidth,keepaspectratio=true]{#1}
	}
}
\newcommand{\showPercentImageNoCaptionRotate}[3]{%
	\unbreakableCenteredBlockSpaced{%
		\includegraphics[width=#2\textwidth,keepaspectratio=true,angle=#3]{#1}
	}
}

\newcommand{\showPercentImage}[3]{%
	\unbreakableCenteredBlockSpaced{%
		\includegraphics[width=#3\textwidth,keepaspectratio=true]{#1}
		\captionof{figure}{#2}
	}
}
%
\newcommand{\showImage}[2]{\showPercentImage{#1}{#2}{1}}
\newcommand{\itemBold}[1]{\item\textbf{#1:}}
