import { h, render } from 'preact'
import Main from './components/Main'
import neo4j from 'neo4j-driver/lib/browser/neo4j-web';

window.addEventListener('load', e => {
	const driver = neo4j.driver(
	  'bolt://localhost:7687',
	  neo4j.auth.basic('neo4j', 'postgres')
	);
	const session = driver.session();
	render(<Main neo4j={session} />, document.getElementById('main'))
})