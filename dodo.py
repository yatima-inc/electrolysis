from doit import create_after
from pathlib import Path

ref = Path('ref')

def task_electrolysis():
    for p in ref.rglob('lib.rs'):
        yield {
            'name': str(p),
            'actions': [['cargo', 'run', p]],
            'file_dep': [p, 'target/debug/electrolysis'],
            'targets': [p.with_name('generated.lean')],
        }

@create_after(executed='electrolysis', target_regex='ref/index\.html')
def task_ref():
    return {
        'actions': ['(cd ref; ./make_ref.py)'],
        'file_dep': ['ref/make_ref.py'] + [p for p in list(ref.rglob('*')) if p.suffix in ['.rs', '.lean', '.md']],
        'targets': ['ref/index.html'],
    }

@create_after(executed='electrolysis')
def task_linja():
    # note: uses ninja depedency management
    return {
        'file_dep': list(ref.rglob('*.lean')),
        'actions': ['(cd ref; linja)'],
    }
