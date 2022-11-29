" Copied from the Go indent file???
if exists('b:did_indent')
  finish
endif
let b:did_indent = 1

setlocal nolisp
setlocal autoindent
setlocal indentexpr=NoulithIndent(v:lnum)
setlocal indentkeys+=<:>,0=},0=)

if exists('*NoulithIndent')
  finish
endif

function! NoulithIndent(lnum)
  let l:prevlnum = prevnonblank(a:lnum-1)
  if l:prevlnum == 0
    " top of file
    return 0
  endif

  " grab the previous and current line, stripping comments.
  let l:prevl = substitute(getline(l:prevlnum), '#.*$', '', '')
  let l:thisl = substitute(getline(a:lnum), '#.*$', '', '')
  let l:previ = indent(l:prevlnum)

  let l:ind = l:previ

  if l:prevl =~ '[[({]\s*$'
    " previous line opened a block
    let l:ind += shiftwidth()
  endif

  if l:thisl =~ '^\s*[])}]'
    " this line closed a block
    let l:ind -= shiftwidth()
  endif

  return l:ind
endfunction

" vim: sw=2 sts=2 et
