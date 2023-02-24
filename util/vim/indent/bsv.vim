" Language:     Bluespec System Verilog (BSV)
" Maintainer:	Hadar Agam <hagam at bluespec dot com >
" Last Change:	Fri Oct 27 12:09:48 EST 2006
"
" Credits:
"   Originally created by
"       Chih-Tsun Huang <cthuang@larc.ee.nthu.edu.tw>
" 	http://larc.ee.nthu.edu.tw/~cthuang/vim/indent/verilog.vim
"
" Buffer Variables:
"     b:verilog_indent_modules : indenting after the declaration
"				 of module blocks
"     b:verilog_indent_width   : indenting width
"     b:verilog_indent_verbose : verbose to each indenting
"

" Only load this indent file when no other was loaded.
if exists("b:did_indent")
  finish
endif
let b:did_indent = 1

setlocal indentexpr=GetBSVIndent()
setlocal indentkeys=!^F,o,O,0),0},=begin,=end,=join,=endcase,=join_any,=join_none
setlocal indentkeys+==endmodule,=endfunction,=endtask,=endspecify
setlocal indentkeys+==endclass,=endpackage,=endsequence,=endclocking,=endrule
setlocal indentkeys+==endmethod,=endinterface,=endgroup,=endprogram,=endproperty
setlocal indentkeys+==`else,=`endif

" Only define the function once.
if exists("*GetBSVIndent")
  finish
endif

set cpo-=C

function GetBSVIndent()

  if exists('b:verilog_indent_width')
    let offset = b:verilog_indent_width
  else
    let offset = &sw
  endif
  if exists('b:verilog_indent_modules')
    let indent_modules = offset
  else
    let indent_modules = 0
  endif

  " Find a non-blank line above the current line.
  let lnum = prevnonblank(v:lnum - 1)

  " At the start of the file use zero indent.
  if lnum == 0
    return 0
  endif

  let lnum2 = prevnonblank(lnum - 1)
  let curr_line  = getline(v:lnum)
  let last_line  = getline(lnum)
  let last_line2 = getline(lnum2)
  let ind  = indent(lnum)
  let ind2 = indent(lnum - 1)
  let offset_comment1 = 1
  " Define the condition of an open statement
  "   Exclude the match of //, /* or */
  let vlog_openstat = '\(\<or\>\|\([*/]\)\@<![*(,{><+-/%^&|!=?:]\([*/]\)\@!\)'
  " Define the condition when the statement ends with a one-line comment
  let vlog_comment = '\(//.*\|/\*.*\*/\s*\)'
  if exists('b:verilog_indent_verbose')
    let vverb_str = 'INDENT VERBOSE:'
    let vverb = 1
  else
    let vverb = 0
  endif

  " Indent according to last line
  " End of multiple-line comment
  if last_line =~ '\*/\s*$' && last_line !~ '/\*.\{-}\*/'
    let ind = ind - offset_comment1
    if vverb
      echo vverb_str "De-indent after a multiple-line comment."
    endif

  " Indent after function/task/class/package/sequence/clocking/
  " rule/method/interface/covergroup/property/program blocks
  elseif last_line =~ '^\s*\<\(function\|task\|class\|package\)\>' ||
    \ last_line =~ '^\s*\<\(sequence\|clocking\|rule\|method\|interface\)\>' ||
    \ last_line =~ '^\s*\(\w\+\s*:\)\=\s*\<covergroup\>' ||
    \ last_line =~ '^\s*\<\(property\|program\)\>'
    if last_line !~ '\<end\>\s*' . vlog_comment . '*$' ||
      \ last_line =~ '\(//\|/\*\).*\(;\|\<end\>\)\s*' . vlog_comment . '*$'

      let is_method = last_line =~ '^\s*\<method\>'
      let is_interface = last_line =~ '^\s*\<interface\>'
      let scopenum = lnum - 1
      let in_module = 0
      let interface_depth = 0
      let found_end_interface = 0
      let found_interface = 0
      while scopenum >= 0 && (is_method || is_interface)
        let scopeline = getline(scopenum)
        if scopeline =~ '^\s*interface\>' && !found_end_interface
          let found_interface = 1
        elseif scopeline =~ '^\s*endinterface\>'
          let found_end_interface = 1
        elseif scopeline =~ '^\s*module\>'
          let in_module = 1
          break
        elseif scopeline =~ '^\s*endmodule\>'
          break
        endif
        let scopenum = scopenum - 1
      endwhile

      if (is_method && in_module) || (is_interface && !found_interface) || (!is_method && !is_interface)
        let ind = ind + offset
        if vverb
          echo vverb_str "Indent after function/task/class block statement."
        endif
      endif
    endif

    " Indent after if/else/for/case/always/initial/specify/fork blocks
  elseif last_line =~ '`\@<!\<\(if\|else\)\>' ||
    \ last_line =~ '^\s*\<\(for\|case\%[[zx]]\|do\|foreach\|randcase\)\>' ||
    \ last_line =~ '^\s*\<\(always\|always_comb\|always_ff\|always_latch\)\>' ||
    \ last_line =~ '^\s*\<\(initial\|specify\|fork\|final\)\>'
    if last_line !~ '\(;\|\<end\>\)\s*' . vlog_comment . '*$' ||
      \ last_line =~ '\(//\|/\*\).*\(;\|\<end\>\)\s*' . vlog_comment . '*$'
      let ind = ind + offset
      if vverb | echo vverb_str "Indent after a block statement." | endif
    endif

  " Indent after module/function/task/specify/fork blocks
  elseif last_line =~ '^\s*\(\<extern\>\s*\)\=\<module\>'
    let ind = ind + indent_modules
    if vverb && indent_modules
      echo vverb_str "Indent after module statement."
    endif
    if last_line =~ '[(,]\s*' . vlog_comment . '*$' &&
      \ last_line !~ '\(//\|/\*\).*[(,]\s*' . vlog_comment . '*$'
      let ind = ind + offset
      if vverb
	echo vverb_str "Indent after a multiple-line module statement."
      endif
    endif

  " Indent after a 'begin' statement
  elseif last_line =~ '\(\<begin\>\)\(\s*:\s*\w\+\)*' . vlog_comment . '*$' &&
    \ last_line !~ '\(//\|/\*\).*\(\<begin\>\)' &&
    \ ( last_line2 !~ vlog_openstat . '\s*' . vlog_comment . '*$' ||
    \ last_line2 =~ '^\s*[^=!]\+\s*:\s*' . vlog_comment . '*$' )
    let ind = ind + offset
    if vverb | echo vverb_str "Indent after begin statement." | endif

  " Indent after a '{' or a '('
  elseif last_line =~ '[{(]' . vlog_comment . '*$' &&
    \ last_line !~ '\(//\|/\*\).*[{(]' &&
    \ ( last_line2 !~ vlog_openstat . '\s*' . vlog_comment . '*$' ||
    \ last_line2 =~ '^\s*[^=!]\+\s*:\s*' . vlog_comment . '*$' )
    let ind = ind + offset
    if vverb | echo vverb_str "Indent after begin statement." | endif

  " De-indent for the end of one-line block
  elseif ( last_line !~ '\<begin\>' ||
    \ last_line =~ '\(//\|/\*\).*\<begin\>' ) &&
    \ last_line2 =~ '\<\(`\@<!if\|`\@<!else\|for\|always\|initial\|do\|foreach\|final\)\>[^;]*' .
    \ vlog_comment . '*$' &&
    \ last_line2 !~ '\(//\|/\*\).*\<\(`\@<!if\|`\@<!else\|for\|always\|initial\|do\|foreach\|final\)\>' &&
    \ last_line2 !~ vlog_openstat . '\s*' . vlog_comment . '*$' &&
    \ ( last_line2 !~ '\<begin\>' ||
    \ last_line2 =~ '\(//\|/\*\).*\<begin\>' )
    let ind = ind - offset
    if vverb
      echo vverb_str "De-indent after the end of one-line statement."
    endif

    " Multiple-line statement (including case statement)
    " Open statement
    "   Ident the first open line
    elseif  last_line =~ vlog_openstat . '\s*' . vlog_comment . '*$' &&
      \ last_line !~ '\(//\|/\*\).*' . vlog_openstat . '\s*$' &&
      \ last_line2 !~ vlog_openstat . '\s*' . vlog_comment . '*$'
      let ind = ind + offset
      if vverb | echo vverb_str "Indent after an open statement." | endif

    " Close statement
    "   De-indent for an optional close parenthesis and a semicolon, and only
    "   if there exists precedent non-whitespace char
    elseif last_line =~ ')*\s*;\s*' . vlog_comment . '*$' &&
      \ last_line !~ '^\s*)*\s*;\s*' . vlog_comment . '*$' &&
      \ last_line !~ '\(//\|/\*\).*\S)*\s*;\s*' . vlog_comment . '*$' &&
      \ ( last_line2 =~ vlog_openstat . '\s*' . vlog_comment . '*$' &&
      \ last_line2 !~ ';\s*//.*$') &&
      \ last_line2 !~ '^\s*' . vlog_comment . '$'
      let ind = ind - offset
      if vverb | echo vverb_str "De-indent after a close statement." | endif

  " `ifdef and `else
  elseif last_line =~ '^\s*`\<\(ifdef\|else\)\>'
    let ind = ind + offset
    if vverb
      echo vverb_str "Indent after a `ifdef or `else statement."
    endif

  endif

  " Re-indent current line

  " De-indent on the end of the block
  " join/end/endcase/endfunction/endtask/endspecify
  if curr_line =~ '^\s*\<\(join\|join_any\|join_none\|\|end\|endcase\|while\)\>' ||
      \ curr_line =~ '^\s*\<\(endfunction\|endtask\|endspecify\|endclass\)\>' ||
    \ curr_line =~ '^\s*\<\(endpackage\|endsequence\|endclocking\|endrule\|endmethod\|endinterface\)\>' ||
      \ curr_line =~ '^\s*\<\(endgroup\|endproperty\|endprogram\)\>' ||
      \ curr_line =~ '^\s*}'
    let ind = ind - offset
    if vverb | echo vverb_str "De-indent the end of a block." | endif
  elseif curr_line =~ '^\s*\<endmodule\>'
    let ind = ind - indent_modules
    if vverb && indent_modules
      echo vverb_str "De-indent the end of a module."
    endif

  " De-indent on a stand-alone 'begin'
  elseif curr_line =~ '^\s*\<begin\>'
    if last_line !~ '^\s*\<\(function\|task\|specify\|module\|class\|package\)\>' ||
      \ last_line !~ '^\s*\<\(sequence\|clocking\|rule\|method\|interface\|covergroup\)\>' ||
      \ last_line !~ '^\s*\<\(property\|program\)\>' &&
      \ last_line !~ '^\s*\()*\s*;\|)\+\)\s*' . vlog_comment . '*$' &&
      \ ( last_line =~
      \ '\<\(`\@<!if\|`\@<!else\|for\|case\%[[zx]]\|always\|initial\|do\|foreach\|randcase\|final\)\>' ||
      \ last_line =~ ')\s*' . vlog_comment . '*$' ||
      \ last_line =~ vlog_openstat . '\s*' . vlog_comment . '*$' )
      let ind = ind - offset
      if vverb
	echo vverb_str "De-indent a stand alone begin statement."
      endif
    endif

  " De-indent after the end of multiple-line statement
  elseif curr_line =~ '^\s*)' &&
    \ ( last_line =~ vlog_openstat . '\s*' . vlog_comment . '*$' ||
    \ last_line !~ vlog_openstat . '\s*' . vlog_comment . '*$' &&
    \ last_line2 =~ vlog_openstat . '\s*' . vlog_comment . '*$' )
    let ind = ind - offset
    if vverb
      echo vverb_str "De-indent the end of a multiple statement."
    endif

  " De-indent `else and `endif
  elseif curr_line =~ '^\s*`\<\(else\|endif\)\>'
    let ind = ind - offset
    if vverb | echo vverb_str "De-indent `else and `endif statement." | endif

  endif

  " Return the indentation
  return ind
endfunction

" vim:sw=2
