import { h, createRef, Component } from 'preact';
import { EditorView, Decoration } from '@codemirror/view';
import { EditorState, StateEffect, StateField } from '@codemirror/state';
import { haskell } from '@codemirror/legacy-modes/mode/haskell'
import { StreamLanguage } from "@codemirror/stream-parser"
import { defaultHighlightStyle } from "@codemirror/highlight"
import { Range, RangeSet } from "@codemirror/rangeset"

const span_msg = StateEffect.define();
const span_deco = Decoration.mark({ class: 'graphie-span', inclusive: true })
const span_ext = StateField.define({
  // Start with an empty set of decorations
  create() { return Decoration.none },
  // This is called whenever the editor updates—it computes the new set
  update(value, tr) {
  	const fx = tr.effects.filter(e => e.is(span_msg));
  	if(fx.length === 1) { // TODO generalize
  		if(fx[0].value.length > 0)
		    return Decoration.set(fx[0].value);
		  else
		  	return Decoration.none;
  	}
	  else
	  	return value;
  },
  // Indicate that this field provides a set of decorations
  provide: f => EditorView.decorations.from(f)
});

function is_graphie_span(e) {
	console.log(e.className)
	return (e.className && e.className.match(/\s*graphie-span\s*/i)) || (e.parentNode && is_graphie_span(e.parentNode))
}
function within([l, h], a) {
	return a >= l && a <= h;
}

export default class extends Component {
	constructor(props) {
		super(props);
		this.state = {
			doc: '',
			doc_id: 0,
			spans: [], // new IntervalTree(),
			cm: null
		};
		this.editor_ref = createRef();
	}
	p2o(p) {
	  return this.state.cm.state.doc.line(p[0]).from + p[1]
	}
	sp2o([l, r]) {
		return [this.p2o(l), this.p2o(r)]
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
		  		EditorView.updateListener.of(this.cmUpdateHandler)
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
					.then(doc => this.setState(s => ({
						doc,
						spans: r.records.map(r_ => {
							const { sp_ch0, sp_chf, sp_l0, sp_lf } = r_.get('a').properties;
							return [[sp_l0.low, sp_ch0.low], [sp_lf.low, sp_chf.low], s.doc_id + 1]; // TODO check if "low" means low byte, or what
						})
					})))
			)
	}
	cmUpdateHandler = updates => {
		if(!updates.changes.empty) {
			this.setState(s => ({ doc_id: s.doc_id + 1 })); // assume by the time this callback is called, cm has updated. hopefully this never de-syncs...
		}
	}
	redecorate_spans() {
		const decos = this.state.spans.filter(([_,__,doc_id]) => doc_id === this.state.doc_id).map(([l, r]) => span_deco.range(this.p2o(l), this.p2o(r)));
		const msgs = span_msg.of(decos);
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
		if(prevState.spans !== this.state.spans || prevState.doc_id !== this.state.doc_id) {
			this.redecorate_spans();
		}
 	}
	handleEditorClick = e => {
		if(is_graphie_span(e.target)) {
			const pos = this.state.cm.posAtCoords({ x: e.clientX, y: e.clientY });
			if(pos !== null) {
				console.log(this.state.spans.filter(sp => within(this.sp2o(sp), pos)));
			}
		}
	}
	render = () => <div ref={this.editor_ref} onClick={this.handleEditorClick}></div>
}