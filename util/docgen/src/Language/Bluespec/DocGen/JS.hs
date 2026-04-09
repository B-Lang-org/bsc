-- | Embedded JavaScript for client-side symbol search.
module Language.Bluespec.DocGen.JS
  ( searchScript
  ) where

import Data.Text (Text)

-- | Vanilla-JS symbol search.  Reads @symbol-index.json@ (relative to the
-- doc root given by @data-root@ on the search input) and populates a
-- dropdown with up to 15 results, prefix matches ranked first.
searchScript :: Text
searchScript = "(function(){\
\'use strict';\
\function init(inp){\
\  var root=inp.dataset.root||'';\
\  var list=inp.nextElementSibling;\
\  var cache=null;\
\  function load(cb){\
\    if(cache){cb(cache);return;}\
\    fetch(root+'symbol-index.json')\
\      .then(function(r){return r.json();})\
\      .then(function(d){\
\        cache=Object.entries(d.symbols||{}).map(function(kv){\
\          return{name:kv[0],pkg:kv[1].display||kv[1].package,url:kv[1].url};\
\        });\
\        cb(cache);\
\      }).catch(function(){cache=[];cb(cache);});\
\  }\
\  function esc(s){\
\    return s.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');\
\  }\
\  function show(ms){\
\    list.innerHTML=ms.length\
\      ?ms.map(function(s){\
\          return '<li><a href=\"'+root+s.url+'\">'\
\               + '<code>'+esc(s.name)+'</code>'\
\               + '<span class=\"bs-pkg\">'+esc(s.pkg)+'</span>'\
\               + '</a></li>';\
\        }).join('')\
\      :'<li class=\"bs-no-match\">No results</li>';\
\    list.hidden=false;\
\  }\
\  function search(q){\
\    if(!q){list.hidden=true;list.innerHTML='';return;}\
\    load(function(syms){\
\      var ql=q.toLowerCase(),pre=[],sub=[];\
\      syms.forEach(function(s){\
\        var n=s.name.toLowerCase();\
\        if(n.startsWith(ql))pre.push(s);\
\        else if(n.includes(ql))sub.push(s);\
\      });\
\      show(pre.concat(sub).slice(0,15));\
\    });\
\  }\
\  inp.addEventListener('input',function(){search(this.value.trim());});\
\  inp.addEventListener('focus',function(){if(this.value.trim())search(this.value.trim());});\
\  document.addEventListener('click',function(e){\
\    if(!inp.parentNode.contains(e.target))list.hidden=true;\
\  });\
\  inp.addEventListener('keydown',function(e){\
\    if(e.key==='Escape'){list.hidden=true;this.blur();}\
\    if(e.key==='Enter'){var a=list.querySelector('a');if(a)window.location.href=a.href;}\
\    if(e.key==='ArrowDown'){e.preventDefault();var a=list.querySelector('a');if(a)a.focus();}\
\  });\
\  list.addEventListener('keydown',function(e){\
\    var ls=Array.from(list.querySelectorAll('a'));\
\    var i=ls.indexOf(document.activeElement);\
\    if(e.key==='ArrowDown'&&i<ls.length-1){e.preventDefault();ls[i+1].focus();}\
\    if(e.key==='ArrowUp'){e.preventDefault();if(i>0)ls[i-1].focus();else inp.focus();}\
\    if(e.key==='Escape'){list.hidden=true;inp.focus();}\
\  });\
\}\
\document.querySelectorAll('.bs-search-input').forEach(init);\
\})();\n\
\/* Anchor link: copy URL on click instead of navigating */\n\
\document.addEventListener('click',function(e){\
\  var a=e.target.closest('.anchor-link');\
\  if(!a)return;\
\  e.preventDefault();\
\  var url=location.origin+location.pathname+a.getAttribute('href');\
\  navigator.clipboard.writeText(url).then(function(){\
\    var old=a.textContent;\
\    a.textContent='copied!';\
\    a.style.opacity='1';\
\    setTimeout(function(){a.textContent=old;a.style.opacity='';},1200);\
\  });\
\});"
