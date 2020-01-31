
bsv-snippets uses google/mit package "yanippits", available for
download free or many debian based packages also allow you to "apt-get
install yasnippets".  A copy is provide here with the original license
agreement..  It's the standard Free Software Foundation GNU GPL..

Feel free to add/modify the bluespec snippets, and even share them
back with us for use in future release :)

This is supported in emacs 22.1 or greater..  Sorry no support for vi
or eclipse at this moment..

=====================================================================
Files:
  .emacs - these are the lines to add to your .emacs file
           you can probably figure out how to move the directory
           to your local area by looking in bsv-mod-and-snippets.el

  bsv-snipppets.el - load snippets directory (called by .emacs lines above)

  bsv-mode/* - all the various snippet files.. 
               see https://code.google.com/p/yasnippet/ for documentation
  
=====================================================================
yasnippets is a means of auto completing certain lines and tasks in
bsv-mode.  It is *not* context sensitive.

The file BsvSnippetSummary.txt describes the words you can type,
followed by a <TAB> and what menu options they bring (if there is more 
than one option), otherwise it will go straight to the code fragments..
The rough format is 
    text =>
       what it expands to

So for the first entry:

    Pulse =>
       PulseWire name <- mkPulseWire;

you type Pulse<TAB> in your buffer (buffer must be in bsv mode), and
this code appears..

   PulseWire name <- mkPulseWire;

With the cursor pointing/highlighting to "name", so you can type in
your own name :)

If there was more than one options, such as for Reg, then a menu will appear
after typing Reg<TAB> which you can select from..

    Reg =>
       Reg#(type) name <- mkRegU;
       Reg#(type) name <- mkReg(defaultValue);
       Reg#(type) name <- mkRegA(defaultValue);

Generally speaking, a bit of code is inserted into your buffer, and
you can type over default variables that are there (and sometimes are
duplicated places - see the "module" snipppet).  <TAB> takes you to
the next field if there is one, and any left/right/up/down keys breaks
you out of the snippet mode..

=======================================================================

the yasnippets elisp package is current available free of charge
from MIT/Google at http://code.google.com/p/yasnippet.

It is provided free of charge and without warrentee or suitability
for any task you specifically have, but of course, we all want this
mode to be more useful, so feel free to add your own entries locally
(and share the good stuff with all :)


=======================================================================
From:

http://opensource.org/licenses/mit-license.php

The MIT License (MIT)
Copyright (c) <year> <copyright holders>

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
