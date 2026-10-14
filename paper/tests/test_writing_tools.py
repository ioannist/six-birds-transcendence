"""W8 manuscript tooling, authored denylist fixtures, and clean TeX regressions."""
import csv
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import zipfile

import pytest

ROOT = Path(__file__).resolve().parents[2]
TOOLS = ROOT/'paper/tools'


def load(name):
    if str(TOOLS) not in sys.path: sys.path.insert(0,str(TOOLS))
    spec=importlib.util.spec_from_file_location('w8_'+name,TOOLS/(name+'.py'))
    module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


FIXTURES=[]
for line in (ROOT/'paper/prewriting/style_denylist.txt').read_text().splitlines():
    match=re.fullmatch(r'# FIXTURE-(PASS|FAIL) (.*)',line)
    if match: FIXTURES.append(pytest.param(match[2],match[1]=='FAIL',id=match[2][:65]))


@pytest.mark.parametrize('text,fail',FIXTURES)
def test_authored_denylist_fixture(text,fail):
    assert bool(load('style_lint').hits(text))==fail


MATH_DELIMITERS=[('$','$'),('$$','$$'),(r'\(',r'\)'),(r'\[',r'\]')]
MATH_DELIMITERS += [(rf'\begin{{{env}{star}}}',rf'\end{{{env}{star}}}')
                    for env in ['equation','align','gather','multline'] for star in ['','*']]


@pytest.mark.parametrize('opening,closing',MATH_DELIMITERS)
def test_math_is_hidden_but_nested_text_is_scanned(opening,closing):
    tool=load('style_lint')
    assert not tool.hits(opening+'G31b'+closing)
    assert tool.hits(opening+r'x+\text{the \emph{G31b} model}'+closing)


def test_comments_citation_and_reference_arguments_are_hidden():
    text=r'We compare this result. \citep[the G31b section][p. 2]{G31b} \cref{PKG-01} \label{G31b}'+'\n% G31b'
    assert not load('style_lint').hits(text)


def test_style_measures_lists_math_and_subjects():
    tool=load('style_lint')
    text=r'We prove our result; it helps us. $x:y;z$ In this paper we compare systems. This paper proves a bound. \begin{itemize}\item Case: a list.\end{itemize} Now: a result.'
    result=tool.measures(text); words=result['words']
    assert result['first_person_per_1000']==pytest.approx(4000/words)
    assert result['paper_agent_per_1000']==pytest.approx(1000/words)
    assert result['semicolons_per_1000']==pytest.approx(1000/words)
    assert result['colons_per_1000']==pytest.approx(1000/words)


@pytest.mark.parametrize('key,value', [('first_person_per_1000',5),('paper_agent_per_1000',1),
    ('semicolons_per_1000',10),('colons_per_1000',13),('mean_sentence_words',27)])
def test_each_style_target_is_enforced(key,value):
    row=dict(words=100,first_person_per_1000=6,paper_agent_per_1000=0,semicolons_per_1000=0,
             colons_per_1000=0,mean_sentence_words=20,denylist_hits=[])
    row[key]=value
    assert key in load('style_lint').target_failures(row)


def style_paper(tmp_path,text):
    (tmp_path/'sections').mkdir()
    (tmp_path/'main.tex').write_text(r'\begin{document}\begin{abstract}We prove a bound.\end{abstract}\input{sections/sec}\end{document}')
    (tmp_path/'sections/sec.tex').write_text(text)
    return tmp_path


@pytest.mark.parametrize('marker',['six-birds-section','artifact-appendix'])
def test_first_line_exemption_and_only_first_line(tmp_path,marker):
    tool=load('style_lint'); paper=style_paper(tmp_path,f'% style-lint: {marker}\nG31b is a toy.')
    result=tool.analyze(paper)
    assert len(result['exempt'])==1 and not result['total']['denylist_hits']
    (paper/'sections/sec.tex').write_text('\n'+(paper/'sections/sec.tex').read_text())
    assert tool.analyze(paper)['total']['denylist_hits']


def test_abstract_body_and_each_caption_are_counted_once(tmp_path):
    tool=load('style_lint'); paper=style_paper(tmp_path,r'We prove a bound. \caption[Short]{We compare branches.}')
    result=tool.analyze(paper)
    assert {r['kind'] for r in result['rows']}=={'abstract','section','caption'}
    assert result['total']['words']==sum(r['words'] for r in result['rows'])
    (paper/'main.tex').write_text((paper/'main.tex').read_text().replace(r'\end{document}',r'\captionof{figure}{G31b caption.}\end{document}'))
    assert any(r['kind']=='caption' and r['denylist_hits'] for r in tool.analyze(paper)['rows'])


def test_included_table_cells_are_dialect_checked_without_prose_metrics(tmp_path,monkeypatch,capsys):
    tool=load('style_lint')
    paper=style_paper(tmp_path,r'We prove our bound. \input{tables/grades}')
    (paper/'tables').mkdir()
    table=paper/'tables/grades.tex'
    table.write_text(r'\begin{table}\caption{Branch conditions.}\begin{tabular}{l}'+'\n'+
                     r'G31b toy \\'+'\n'+r'\end{tabular}\end{table}'+'\n')
    report=tool.analyze(paper)
    body=next(row for row in report['rows'] if row['kind']=='table')
    assert body['words']==0 and body['failed_targets']==['denylist_hits']
    assert {'G31b','toy'} <= {hit['match'] for hit in body['denylist_hits']}
    assert all(Path(hit['file'])==table for hit in body['denylist_hits'])
    assert report['total']['words']==10  # abstract + section + caption only
    assert sum(row['kind']=='caption' for row in report['rows'])==1
    monkeypatch.setattr(sys,'argv',['style_lint.py',str(paper),'--strict'])
    assert tool.main()==1
    table.write_text(table.read_text().replace('G31b toy','Computed condition'))
    assert tool.main()==0
    assert tool.analyze(paper)['total']['words']==10
    capsys.readouterr()


def test_wrapped_abstract_keywords_are_not_prose_but_keep_denylist_checks(tmp_path,monkeypatch,capsys):
    tool=load('style_lint')
    (tmp_path/'sections').mkdir()
    (tmp_path/'main.tex').write_text(r'\begin{document}\input{sections/abstract}\end{document}')
    abstract=tmp_path/'sections/abstract.tex'
    abstract.write_text(r'\begin{abstract}We prove our bound.\end{abstract}'+'\n\n'+
                        r'\noindent\textbf{Keywords.} continuation, personal identity,'+'\n'+
                        'viability, finite models.\n')
    report=tool.analyze(tmp_path)
    assert report['total']['words']==4
    assert not any(row['failed_targets'] for row in [*report['rows'],report['total']])
    monkeypatch.setattr(sys,'argv',['style_lint.py',str(tmp_path),'--strict'])
    assert tool.main()==0
    abstract.write_text(abstract.read_text().replace('finite models','toy models'))
    report=tool.analyze(tmp_path)
    assert report['total']['words']==4
    assert any(hit['match']=='toy' for hit in report['total']['denylist_hits'])
    assert tool.main()==1
    capsys.readouterr()


@pytest.mark.parametrize('boundary',['\n\n',r'\par'+'\n'])
def test_keywords_mask_does_not_hide_following_prose(boundary):
    tool=load('style_lint')
    prefix=r'\noindent\textbf{Keywords.} continuation, identity,'+'\n'+'finite models.'
    text=prefix+boundary+'We prove our bound.'
    assert tool.measures(text)==tool.measures('We prove our bound.')


def test_report_and_strict_modes(tmp_path,monkeypatch,capsys):
    tool=load('style_lint'); paper=style_paper(tmp_path,'We describe a toy.')
    monkeypatch.setattr(sys,'argv',['style_lint.py',str(paper)])
    assert tool.main()==0
    monkeypatch.setattr(sys,'argv',['style_lint.py',str(paper),'--strict'])
    assert tool.main()==1
    capsys.readouterr()


def test_caption_without_first_person_passes_strict_but_denylist_still_fails(tmp_path,monkeypatch,capsys):
    tool=load('style_lint')
    paper=style_paper(tmp_path,r'We prove our bound. \caption{Predictive readouts agree at the endpoint.}')
    monkeypatch.setattr(sys,'argv',['style_lint.py',str(paper),'--strict'])
    assert tool.main()==0
    caption=next(row for row in tool.analyze(paper)['rows'] if row['kind']=='caption')
    assert caption['first_person_per_1000']==0 and not caption['failed_targets']
    source=paper/'sections/sec.tex'
    source.write_text(source.read_text().replace('Predictive readouts agree at the endpoint.','A toy.'))
    assert tool.main()==1
    capsys.readouterr()


@pytest.mark.parametrize('key,value', [('paper_agent_per_1000',1),('semicolons_per_1000',10),
    ('colons_per_1000',13),('mean_sentence_words',27),('denylist_hits',[{'match':'toy'}])])
def test_caption_exemption_keeps_every_other_target(key,value):
    tool=load('style_lint')
    row=dict(kind='caption',words=100,first_person_per_1000=0,paper_agent_per_1000=0,
             semicolons_per_1000=0,colons_per_1000=0,mean_sentence_words=20,denylist_hits=[])
    assert not tool.target_failures(row)
    assert tool.target_failures(dict(row,kind='section'))==['first_person_per_1000']
    row[key]=value
    assert tool.target_failures(row)==[key]


def fixture_paper(tmp_path,text):
    for directory in ['sections','prewriting','figures/generated']:(tmp_path/directory).mkdir(parents=True)
    (tmp_path/'main.tex').write_text(r'\begin{document}\input{sections/sec}\end{document}')
    (tmp_path/'sections/sec.tex').write_text(text)
    (tmp_path/'prewriting/references_core.bib').write_text('@misc{Known, title={Known}}\n')
    (tmp_path/'prewriting/references_sixbirds.bib').write_text('@misc{Corpus, title={Corpus}}\n')
    (tmp_path/'prewriting/claim_ledger.csv').write_text('claim_id\nTTH-01\nTTH-02\n')
    (tmp_path/'figures/generated/figdata.tex').write_text(r'\newcommand{\snapExample}{\ensuremath{8}}')
    return tmp_path


def test_concept_figure_fixed_structural_ordinals(tmp_path):
    paper=fixture_paper(tmp_path,r'\input{figures/fig_three}')
    (paper/'figures/fig_three.tex').write_text(
        r'\newcommand{\episodeStageOne}{1}'+r'\begin{tikzpicture}\node{\episodeStageOne};\end{tikzpicture}')
    assert not load('check_manuscript').check(paper)['errors']


@pytest.mark.parametrize('mutation',['value','argument','elsewhere','outside_use'])
def test_schematic_ordinals_cannot_supply_general_numeric_values(tmp_path,mutation):
    paper=fixture_paper(tmp_path,r'\input{figures/fig_three}')
    definition=r'\newcommand{\episodeStageOne}{1}'
    if mutation=='value': definition=r'\newcommand{\episodeStageOne}{99}'
    if mutation=='argument': definition=r'\newcommand{\episodeStageOne}[1]{1}'
    if mutation=='elsewhere':
        (paper/'sections/sec.tex').write_text(definition+r'\input{figures/fig_three}');definition=''
    if mutation=='outside_use':
        (paper/'sections/sec.tex').write_text(r'\input{figures/fig_three}\begin{tikzpicture}\node{\episodeStageOne};\end{tikzpicture}')
    (paper/'figures/fig_three.tex').write_text(definition+r'\begin{tikzpicture}\node{\episodeStageOne};\end{tikzpicture}')
    assert load('check_manuscript').check(paper)['errors']


@pytest.mark.parametrize('prefix,body',[
    ('',r'\node{probability \episodeStageOne/\episodeStageFour};'),
    ('',r'\node{measured count \episodeStageThree};'),
    ('',r'\node{\episodeStageOne/\episodeStageFour};'),
    ('',r'\node{\textbf{\episodeStageThree}};'),
    ('',r'\node[label=above:{\episodeStageThree}]{target};'),
    (r'\newcommand{\alias}{\episodeStageThree}',r'\node{\alias};'),
    (r'\let\episodeStageThree\snapExample',r'\node{\episodeStageThree};'),
    ('',r'\node{\episodeStageTwo};'),  # no local definition
])
def test_concept_ordinals_are_only_complete_literal_node_bodies(tmp_path,prefix,body):
    paper=fixture_paper(tmp_path,r'\input{figures/fig_three}')
    definitions=(r'\newcommand{\episodeStageOne}{1}'
                 r'\newcommand{\episodeStageThree}{3}'
                 r'\newcommand{\episodeStageFour}{4}')
    (paper/'figures/fig_three.tex').write_text(
        definitions+prefix+r'\begin{tikzpicture}'+body+r'\end{tikzpicture}')
    assert load('check_manuscript').check(paper)['errors']


@pytest.mark.parametrize('text',[
    r'\citep[see][p. 2]{Missing}',r'\cite*{Known,Missing}',r'\citet{Missing}',
])
def test_unknown_citation_is_rejected(tmp_path,text):
    result=load('check_manuscript').check(fixture_paper(tmp_path,text))
    assert any('unknown citation' in e for e in result['errors'])


def test_known_citations_and_reference_labels(tmp_path):
    text=r'\citep[see][p. 2]{Known,Corpus}\label{sec:yes}'
    tool=load('check_manuscript'); paper=fixture_paper(tmp_path,text)
    result=tool.check(paper)
    assert not result['errors'] and result['section_labels']==['sec:yes']
    assert not tool.check(paper,{'intro':'sec:yes'})['errors']
    assert any('missing section label' in e for e in tool.check(paper,{'intro':'sec:missing'})['errors'])


@pytest.mark.parametrize('environment',['theorem','lemma','proposition','corollary','definition'])
def test_claim_tag_required_for_each_environment(tmp_path,environment):
    paper=fixture_paper(tmp_path,rf'\begin{{{environment}}}'+'\nBody.\n'+rf'\end{{{environment}}}')
    assert any('needs a claim comment' in e for e in load('check_manuscript').check(paper)['errors'])


@pytest.mark.parametrize('tag',['% claim: DoesNotExist','', '% claim: TTH-01, DoesNotExist'])
def test_invalid_or_missing_claim_id_is_rejected(tmp_path,tag):
    text='\\begin{theorem}\n'+tag+'\nBody.\n\\end{theorem}'
    assert load('check_manuscript').check(fixture_paper(tmp_path,text))['errors']


def test_valid_multiple_claims_and_comment_position(tmp_path):
    text='\\begin{theorem}[A bound]\n% claim: TTH-01, TTH-02\nBody.\n\\end{theorem}'
    paper=fixture_paper(tmp_path,text); tool=load('check_manuscript')
    assert not tool.check(paper)['errors']
    (paper/'sections/sec.tex').write_text(text.replace('\n% claim:',' % claim:'))
    assert tool.check(paper)['errors']


@pytest.mark.parametrize('label',[
    r'\node at (1,2) {3};',r'\draw (0,0) -- (2,1) node[midway] {$1/8$};',
    r'\node[label=above:{2}] (n) {Text};',r'\node {\snapMissing};',
    r'\newcommand{\hidden}{8}\node {\hidden};',
    r'\foreach \i in {1,2} \node {\i};',
    r'\renewcommand{\snapExample}{9}\node {\snapExample};',
])
def test_unpinned_numeric_node_labels_are_rejected(tmp_path,label):
    text=r'\begin{tikzpicture}'+label+r'\end{tikzpicture}'
    assert load('check_manuscript').check(fixture_paper(tmp_path,text))['errors']


def test_coordinates_and_generated_macro_labels_are_allowed(tmp_path):
    text=r'\begin{tikzpicture}\node[draw] (n) at (1.5,2) {\textbf{\snapExample}};\end{tikzpicture}'
    assert not load('check_manuscript').check(fixture_paper(tmp_path,text))['errors']


def test_current_manuscript_passes():
    result=subprocess.run([sys.executable,str(TOOLS/'check_manuscript.py')],capture_output=True,text=True)
    assert result.returncode==0,result.stdout+result.stderr


def test_all_snapshot_entries_have_unique_tex_safe_macros():
    tool=load('render_figure_data'); snapshot=json.loads((ROOT/'paper/data/current_results.json').read_text())
    macros=tool.macros(snapshot)
    assert len(macros)==len(snapshot['entries'])
    assert all(re.fullmatch(r'[A-Za-z]+',name) for _,name,_ in macros)
    assert len({name for _,name,_ in macros})==len(macros)
    assert tool.number_tex('3/8')==r'\frac{3}{8}'
    assert tool.macro_name('g7_strict_chain_system_ids')=='snapGSevenStrictChainSystemIds'


def test_figure_data_check_passes():
    result=subprocess.run([sys.executable,str(TOOLS/'render_figure_data.py'),'--check'],capture_output=True,text=True)
    assert result.returncode==0,result.stdout+result.stderr


def test_figure_data_drift_and_collision(tmp_path,monkeypatch,capsys):
    tool=load('render_figure_data'); data={'entries':[dict(key='x1',value='3/8',value_type='rational')]}
    source=tmp_path/'snapshot.json'; source.write_text(json.dumps(data)); output=tmp_path/'figdata.tex'
    monkeypatch.setattr(tool,'SNAPSHOT',source); monkeypatch.setattr(tool,'OUTPUT',output)
    monkeypatch.setattr(sys,'argv',['render_figure_data.py'])
    assert tool.main()==0
    monkeypatch.setattr(sys,'argv',['render_figure_data.py','--check'])
    assert tool.main()==0
    output.write_text(output.read_text()+'\n'); before=output.read_bytes()
    assert tool.main()==1 and output.read_bytes()==before
    data['entries'].append(dict(key='x_one',value='1',value_type='integer'))
    with pytest.raises(ValueError,match='collision'):tool.macros(data)
    capsys.readouterr()


def run(command,cwd):
    result=subprocess.run(command,cwd=cwd,capture_output=True,text=True)
    assert result.returncode==0,(result.stdout+result.stderr)[-1800:]
    return result


@pytest.mark.parametrize('citation_location',['none','appendix'])
def test_bibliography_clean_build_and_automatic_activation(tmp_path,citation_location):
    files=['main.tex','latexmkrc','includes/paper_macros.tex','includes/release_counts.tex',
           'includes/release_metadata.tex','figures/generated/figdata.tex',
           'prewriting/references_core.bib','prewriting/references_sixbirds.bib']
    for name in files:
        target=tmp_path/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/'paper'/name,target)
    main=tmp_path/'main.tex'
    main.write_text(re.sub(r'\\input\{(?:sections|appendices)/[^}]+\}', '', main.read_text()).replace(
        r'\appendix', r'\appendix'+'\n'+r'\input{appendices/fixture.tex}'))
    document=main.read_text().split(r'\begin{document}',1)[1]
    assert document.index(r'\input{appendices/fixture.tex}') < document.index(r'\ifpaperHasCitations')
    appendix=tmp_path/'appendices/fixture.tex';appendix.parent.mkdir(parents=True,exist_ok=True);appendix.write_text('% fixture\n')
    key=next(iter(sorted(load('check_manuscript').bib_keys(tmp_path/'prewriting/references_core.bib'))))
    if citation_location=='appendix': appendix.write_text(r'\citep{'+key+'}\n')
    result=run(['latexmk'],tmp_path)
    assert (tmp_path/'build/main.pdf').is_file()
    metadata=load('check_manuscript').macro_definitions((tmp_path/'includes/release_metadata.tex').read_text())
    rendered=subprocess.check_output(['pdftotext',str(tmp_path/'build/main.pdf'),'-'],text=True)
    for field in ['paperdoi','manuscriptversion','manuscriptdate']:
        assert metadata[field] in rendered
    assert '\u00a9 '+metadata['manuscriptyear'] in rendered and 'CC-BY 4.0' in rendered
    aux=(tmp_path/'build/main.aux').read_text();log=(tmp_path/'build/main.log').read_text()
    assert 'undefined references' not in log and 'Overfull' not in log
    if citation_location=='none': assert r'\bibdata' not in aux and not (tmp_path/'build/main.bbl').exists()
    else:
        assert r'\bibcite{'+key in aux
        assert 'prewriting/references_core,prewriting/references_sixbirds' in aux
        assert 'bibtex' in result.stdout.lower()


def test_bibliography_follows_all_five_appendices():
    document=(ROOT/'paper/main.tex').read_text().split(r'\begin{document}',1)[1]
    appendices=re.findall(r'\\input\{appendices/([^}]+)\}',document)
    assert appendices==['app_a_sixbirds','app_b_models','app_c_index',
                       'app_d_proofs','app_e_reproducibility']
    last=document.index(r'\input{appendices/app_e_reproducibility}')
    guard=document.index(r'\ifpaperHasCitations')
    clear=document.index(r'\clearpage',guard)
    style=document.index(r'\bibliographystyle{plainnat}',guard)
    bibliography=document.index(r'\bibliography{prewriting/references_core,prewriting/references_sixbirds}',guard)
    assert last < guard < clear < style < bibliography < document.index(r'\fi',bibliography)


def test_review_archive_is_head_only_and_latest_version(tmp_path):
    (tmp_path/'scripts').mkdir();shutil.copyfile(ROOT/'scripts/make_review_zip.sh',tmp_path/'scripts/make_review_zip.sh')
    (tmp_path/'paper').mkdir();(tmp_path/'paper/main.pdf').write_bytes(b'%PDF fixture')
    (tmp_path/'review_requests').mkdir()
    for v in ['v2','v10']:(tmp_path/f'review_requests/external_review_request_{v}.md').write_text('% test request\n')
    run(['git','init','-q'],tmp_path);run(['git','add','.'],tmp_path)
    run(['git','-c','user.name=Fixture','-c','user.email=fixture@example.invalid','commit','-qm','Fixture'],tmp_path)
    (tmp_path/'paper/main.pdf').write_bytes(b'uncommitted replacement')
    (tmp_path/'untracked.txt').write_text('excluded')
    result=run(['bash','scripts/make_review_zip.sh'],tmp_path)
    assert 'PDF: paper/main.pdf' in result.stdout
    with zipfile.ZipFile(tmp_path/'review_requests/six-birds-transcendence_v10.zip') as archive:
        assert archive.read('paper/main.pdf')==b'%PDF fixture'
        assert 'untracked.txt' not in archive.namelist()


def test_review_archive_missing_version_and_ignore_rule(tmp_path):
    (tmp_path/'scripts').mkdir();shutil.copyfile(ROOT/'scripts/make_review_zip.sh',tmp_path/'scripts/make_review_zip.sh')
    result=subprocess.run(['bash','scripts/make_review_zip.sh'],cwd=tmp_path,capture_output=True,text=True)
    assert result.returncode==2 and 'external_review_request_vNN.md' in result.stderr
    # An exported source archive has no .git. Exercise the actual ignore rules
    # in the temporary fixture instead of requiring a checkout around ROOT.
    shutil.copyfile(ROOT/'.gitignore',tmp_path/'.gitignore')
    run(['git','init','-q'],tmp_path)
    result=subprocess.run(['git','check-ignore','review_requests/fixture.zip'],cwd=tmp_path,capture_output=True,text=True)
    assert result.returncode==0


def test_nested_math_in_visible_text_preserves_dialect():
    tool=load('style_lint')
    hits=tool.hits(r'$x+\text{a toy in $G_2$}$')
    assert any(h['match']=='toy' for h in hits)
    assert not any('G_2' in h['match'] for h in hits)


@pytest.mark.parametrize('slashes', [0,2,4])
def test_even_backslash_parity_opens_math(slashes):
    assert not load('style_lint').hits('\\'*slashes+'$G31b$')


def test_odd_backslash_parity_is_literal_dollar():
    assert load('style_lint').hits(r'\$G31b is visible prose.')


@pytest.mark.parametrize('text',[
    r'\section{The G31b toy}',
    r'\begin{tabular}{l}The G31b toy\\\end{tabular}',
    r'\begin{tikzpicture}\node{The G31b toy};\end{tikzpicture}',
])
def test_visible_headings_tables_and_labels_are_dialect_checked(text):
    tool=load('style_lint')
    assert any(h['match']=='G31b' for h in tool.hits(text))
    assert any(h['match']=='toy' for h in tool.hits(text))
    assert tool.measures(text)['words']==0


@pytest.mark.parametrize('text',[
    r'\newcommand\hidden{9}\begin{tikzpicture}\node{\hidden};\end{tikzpicture}',
    r'\renewcommand\snapExample{99}\begin{tikzpicture}\node{\snapExample};\end{tikzpicture}',
    r'\begin{tikzpicture}\node[label=above:{\snapExample,9}]{Clean};\end{tikzpicture}',
    r'\newcommand\drawing{\node{9};}\begin{tikzpicture}\drawing\end{tikzpicture}',
    r'\newcommand\drawing[1]{\node{#1};}\begin{tikzpicture}\drawing{9}\end{tikzpicture}',
])
def test_eddy_numeric_macro_and_option_bypasses_rejected(tmp_path,text):
    assert load('check_manuscript').check(fixture_paper(tmp_path,text))['errors']


def test_input_fragment_inherits_enclosing_tikz_context(tmp_path):
    paper=fixture_paper(tmp_path,r'\begin{tikzpicture}\input{figures/fragment}\end{tikzpicture}')
    fragment=paper/'figures/fragment.tex';fragment.write_text(r'\node at (1,2){9};')
    assert load('check_manuscript').check(paper)['errors']
    fragment.write_text(r'\node at (1,2){\snapExample};')
    assert not load('check_manuscript').check(paper)['errors']


def test_nested_invoked_drawing_macros_cannot_hide_nodes(tmp_path):
    text=r'\newcommand\inner{\node{9};}\newcommand\outer{\inner}\begin{tikzpicture}\outer\end{tikzpicture}'
    assert load('check_manuscript').check(fixture_paper(tmp_path,text))['errors']


def test_declared_drawing_arguments_can_use_snapshot_values(tmp_path):
    text=r'\newcommand\drawing[1]{\node at (1,2){#1};}\begin{tikzpicture}\drawing{\snapExample}\end{tikzpicture}'
    assert not load('check_manuscript').check(fixture_paper(tmp_path,text))['errors']


def test_unsupported_dynamic_tikz_is_explicitly_rejected(tmp_path):
    text=r'\begin{tikzpicture}\pgfmathsetmacro{\hidden}{9}\node{\hidden};\end{tikzpicture}'
    errors=load('check_manuscript').check(fixture_paper(tmp_path,text))['errors']
    assert any('Unsupported' in e and ('hidden' in e or 'pgfmathsetmacro' in e) for e in errors)


def test_citetext_is_prose_and_nested_citealp_takes_keys(tmp_path):
    paper=fixture_paper(tmp_path,r'\citetext{See \citealp{Cerullo2015}}')
    with (paper/'prewriting/references_core.bib').open('a') as out:out.write('@misc{Cerullo2015, title={Known}}\n')
    assert not load('check_manuscript').check(paper)['errors']
    assert load('style_lint').hits(r'\citetext{The G31b toy; see \citealp{Known}}')


def test_nocite_missing_key_rejected_and_star_allowed(tmp_path):
    paper=fixture_paper(tmp_path,r'\nocite{W8Missing}')
    assert any('unknown citation' in e and 'W8Missing' in e for e in load('check_manuscript').check(paper)['errors'])
    (paper/'sections/sec.tex').write_text(r'\nocite{*}\nocite{Known,Corpus}')
    assert not load('check_manuscript').check(paper)['errors']


def test_unknown_label_macro_is_not_assumed_safe(tmp_path):
    text=r'\let\alias\unknown\begin{tikzpicture}\node{\alias};\end{tikzpicture}'
    assert any('Unsupported' in e and 'alias' in e for e in load('check_manuscript').check(fixture_paper(tmp_path,text))['errors'])


def test_repeated_macro_declaration_is_explicitly_unsupported(tmp_path):
    text=r'\newcommand\hidden{9}\begin{tikzpicture}\node{\hidden};\renewcommand\hidden{\snapExample}\end{tikzpicture}'
    with pytest.raises(ValueError,match='Unsupported repeated macro declaration'):
        load('check_manuscript').check(fixture_paper(tmp_path,text))


def test_figure_file_visible_labels_are_checked_in_production_analysis(tmp_path):
    paper=style_paper(tmp_path,r'We draw a figure. \input{figures/example}')
    (paper/'figures').mkdir()
    (paper/'figures/example.tex').write_text(r'\begin{tikzpicture}\node (safe) {The G31b toy};\end{tikzpicture}')
    result=load('style_lint').analyze(paper)
    assert any(row['kind']=='figure' and row['denylist_hits'] for row in result['rows'])
    assert any(hit['match']=='G31b' for hit in result['total']['denylist_hits'])


def test_invisible_tikz_coordinate_identifiers_are_not_prose():
    text=r'\begin{tikzpicture}\node (G31b) at (1,2) {Safe};\end{tikzpicture}'
    assert not load('style_lint').hits(text)


def test_word_node_inside_label_is_plain_prose(tmp_path):
    text=r'\begin{tikzpicture}\node{The output node};\end{tikzpicture}'
    assert not load('check_manuscript').check(fixture_paper(tmp_path,text))['errors']


def test_global_let_cannot_replace_a_snapshot_macro(tmp_path):
    text=r'\newcommand\nine{9}\let\snapExample\nine\begin{tikzpicture}\node{\snapExample};\end{tikzpicture}'
    assert any('reassigned' in e for e in load('check_manuscript').check(fixture_paper(tmp_path,text))['errors'])
