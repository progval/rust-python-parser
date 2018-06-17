#!/usr/bin/env python3
import os
import sys
import ast
import time
import difflib
import tempfile
import unittest
import astpretty
import subprocess
import threading
import multiprocessing

def test_file(path):
    with open(path) as f:
        expected_ast = astpretty.pformat(ast.parse(f.read()), show_offsets=False)
    before = time.time()
    printer_output = subprocess.check_output(['./target/release/prettyprint', path])
    total_time = time.time() - before
    try:
        received_ast = astpretty.pformat(ast.parse(printer_output), show_offsets=False)
    except:
        print('Error while parsing the output from {}:'.format(path))
        raise
    if expected_ast == received_ast:
        print('({:03}ms) {}: ok'.format(int(total_time*1000), path))
        return
    print('========================')
    print(path)
    print('------------------------')
    #for line in difflib.unified_diff(received_ast, expected_ast): # OMG so slow
    #    print(line)
    with tempfile.NamedTemporaryFile('w+', prefix='expected-') as exp_file, \
            tempfile.NamedTemporaryFile('w+', prefix='received-') as received_file:
        exp_file.write(expected_ast)
        exp_file.seek(0)
        received_file.write(received_ast)
        received_file.seek(0)
        try:
            subprocess.check_output(
                    ['diff', '-u', received_file.name, exp_file.name],
                    universal_newlines=True)
        except subprocess.CalledProcessError as e:
            print(e.output)
        else:
            assert False, 'diff did not detect a different, but should have.'
    print('========================')
    exit(1)

def test_dir(path, with_threads=False):
    sem = threading.BoundedSemaphore(value=multiprocessing.cpu_count())
    def thread(path):
        sem.acquire()
        try:
            test_file(path)
        finally:
            sem.release()

    for (dirpath, dirname, filenames) in os.walk(path):
        if any(x.startswith('.') for x in dirpath.split(os.path.sep)):
            # dotfile
            continue
        for filename in filenames:
            if os.path.splitext(filename)[1] == '.py':
                if with_threads:
                    threading.Thread(target=thread, args=(os.path.join(dirpath, filename),)).start()
                else:
                    test_file(os.path.join(dirpath, filename))



def main():
    if '--with-threads' in sys.argv:
        sys.argv.remove('--with-threads')
        with_threads = True
    else:
        with_threads = False
    subprocess.check_output(['cargo', 'build'])
    #subprocess.check_output(['cargo', 'build', '--release'])
    for path in sys.argv[1:]:
        if os.path.isfile(path):
            test_file(path)
        elif os.path.isdir(path):
            test_dir(path, with_threads=with_threads)
        else:
            print('Error: no such file or directory: {}'.format(path))
            exit(1)

if __name__ == '__main__':
    main()
