import { h, createRef, Component } from 'preact';
import { EditorView, Decoration } from '@codemirror/view';
import { EditorState, StateEffect, StateField } from '@codemirror/state';
import { haskell } from '@codemirror/legacy-modes/mode/haskell'
import { StreamLanguage } from "@codemirror/stream-parser"
import { defaultHighlightStyle } from "@codemirror/highlight"
import { Range, RangeSet } from "@codemirror/rangeset"
import IntervalTree from '@flatten-js/interval-tree'

const span_msg = StateEffect.define();
const span_deco = Decoration.mark({ class: 'graphie-span' })
const span_ext = StateField.define({
  // Start with an empty set of decorations
  create() { return Decoration.none },
  // This is called whenever the editor updates—it computes the new set
  update(value, tr) {
  	const fx = tr.effects.filter(e => e.is(span_msg));
  	if(fx.length === 1) { // TODO generalize
  		if(fx[0].value.length > 0)
		    return Decoration.set(fx[0].value);
  	}
	  else
	  	return value;
  },
  // Indicate that this field provides a set of decorations
  provide: f => EditorView.decorations.from(f)
});

function mk_itree(is) {
	const T = new IntervalTree();
	for(const i of is) {
		T.insert(...(Array.isArray(i) ? i : [i]));
	}
	return T;
}

export default class extends Component {
	constructor(props) {
		super(props);
		this.state = {
			doc: '',
			spans: [], // new IntervalTree(),
			cm: null
		};
		this.editor_ref = createRef();
	}
	sp2o(sp) {
	  return this.state.cm.state.doc.line(sp[0]).from + sp[1]
	}
	componentDidMount() {
		const deco = Decoration.mark({ class: 'marked', tagName: 'span', inclusive: true });
		const cm = new EditorView({
		  state: EditorState.create({
		  	doc: this.state.doc,
		  	extensions: [
		  		StreamLanguage.define(haskell),
		  		defaultHighlightStyle.fallback,
		  		span_ext,
		  		// EditorView.decorations.of(Decoration.set([
		  		// 		deco.range(1, 3),
		  		// 		deco.range(2, 4),
		  		// 	]))
	  		],
		  	readOnly: true
		  }),
		  parent: this.editor_ref.current
		});
		// TODO map all incoming spans to pos via codemirror, use pos-coordinates everywhere
		this.setState({ cm }) // , _ => this.redecorate_spans());
		
		this.props.neo4j.run('MATCH (a) WHERE id(a) = 5 RETURN a;')
			.then(r =>
				fetch(r.records[0].get('a').properties.sp_fn.replace(/^\/*src\//i, '/'))
					.then(s => s.text())
					.then(doc => this.setState({
						doc,
						spans: r.records.map(r_ => {
							const { sp_ch0, sp_chf, sp_l0, sp_lf } = r_.get('a').properties;
							return [[sp_l0.low, sp_ch0.low], [sp_lf.low, sp_chf.low]]; // TODO check if "low" means low byte, or what
						})
					}))
			)
	}
	redecorate_spans() {
		const decos = this.state.spans.map(([l, r]) => span_deco.range(this.sp2o(l), this.sp2o(r)));
		console.log(decos)
		const msgs = span_msg.of(decos); // TODO make sure `of` is non-mutating
		// TODO have to wait for any doc changes to settle before converting the spans from line-ch formats to pos formats via callback on transactions
		this.state.cm.dispatch({ effects: msgs });
	}
	replace_doc() {
		this.state.cm.dispatch({ changes: {
			from: 0,
			to: this.state.cm.state.doc.length,
			insert: this.state.doc
		} });
	}
	componentDidUpdate(prevProps, prevState) {
		if(prevState.doc !== this.state.doc) {
			this.replace_doc();
		}
		if(prevState.spans !== this.state.spans) {
			this.redecorate_spans();
		}
 	}
	handleEditorClick = e => {
		if(e.target.className.match(/\s+graphie-span\s+/i)) {
			const pos = this.state.cm.posAtCoords({ x: e.clientX, y: e.clientY });
			if(pos !== null) {
				this.state.spans.search([pos, pos]);
			}
		}
	}
	render = () => <div ref={this.editor_ref} onClick={this.handleEditorClick}></div>
}