const express = require('express');
const bodyParser = require('body-parser');
const XeroClient = require('xero-node').XeroClient;

const app = express();
const port = process.env.PORT || 3000;

app.use(bodyParser.json());

app.get('/', (req, res) => {
    res.send('Hello from xero-bot!');
});

app.listen(port, () => {
    console.log(`Server is running on http://localhost:${port}`);
});