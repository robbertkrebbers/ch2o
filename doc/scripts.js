window.onload = function() {
  var elems = document.getElementsByTagName('span');
  for(i in elems) {
    if(elems[i].className != 'toggleproof')
      continue;

    elems[i].onclick = function() {
      var e = this;
      while(e.nodeType !== 1 || e.className != "proofscript")
        e = e.nextSibling

      if (e.style.display != 'inline')
        e.style.display = 'inline';
      else
        e.style.display = 'none';
    }
  }
}
