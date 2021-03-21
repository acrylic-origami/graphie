const express = require('express');
const app = express();
app.use(express.static('public'));
app.use(express.static('../vendor/hie/'));

app.listen(9010);
