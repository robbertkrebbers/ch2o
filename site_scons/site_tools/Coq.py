# Copyright (c) 2012-2015, Robbert Krebbers.
# This file is distributed under the terms of the BSD license.
import SCons.Defaults, SCons.Tool, SCons.Util, os

def coq_emitter(target, source, env):
  base, _ = os.path.splitext(str(target[0]))
  for ext in ['.glob', '.vos', '.vok']:
    target.append(base + ext)
  return target, source
Coq = SCons.Builder.Builder(
  action = '$COQC $COQFLAGS -q $SOURCE',
  suffix = '.vo',
  src_suffix = '.v',
  emitter = coq_emitter
)

def make_coqidescript(target, source, env):
  open('coqidescript', 'w').write('#!/bin/sh\n' +
    env['COQIDE'] + ' ' + env['COQFLAGS'] + ' $@ \n')
  os.chmod('coqidescript', 0o755)
  return 0
CoqIdeScript = SCons.Builder.Builder(action = make_coqidescript)

def generate(env):
  env['COQC'] = 'coqc'
  env['COQIDE'] = 'coqide'
  env.Append(BUILDERS = {
    'Coq' : Coq, 'CoqIdeScript' : CoqIdeScript
  })

def exists(env):
  return env.Detect('coqc')
