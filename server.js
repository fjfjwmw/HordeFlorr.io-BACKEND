// server.js

const express = require('express');
const bodyParser = require('body-parser');
const cors = require('cors');

const app = express();
app.use(cors());
app.use(bodyParser.json());

// Critical bug fixes
// Fix for leaderboard snapshots
let leaderboardSnapshots = [];
const saveLeaderboardSnapshot = (snapshot) => {
    leaderboardSnapshots.push(snapshot);
    // Ensure we limit the number of snapshots stored
    if (leaderboardSnapshots.length > 10) {
        leaderboardSnapshots.shift(); // Remove the oldest snapshot
    }
};

// Fix for random spawn fallback logic
const randomSpawn = (spawns) => {
    if (!Array.isArray(spawns) || spawns.length === 0) {
        return {x: 0, y: 0}; // Default fallback spawn
    }
    const randomIndex = Math.floor(Math.random() * spawns.length);
    return spawns[randomIndex];
};

// Fix for queue countdown race condition
let queueCountdown = 10;
let countdownInterval;
const startCountdown = () => {
    clearInterval(countdownInterval);
    queueCountdown = 10;
    countdownInterval = setInterval(() => {
        if (queueCountdown > 0) {
            queueCountdown--;
        } else {
            clearInterval(countdownInterval);
            // Code to handle when countdown reaches zero
afterCountdownHandler();
        }
    }, 1000);
};

const afterCountdownHandler = () => {
    // Your logic here for what happens after countdown ends
};

app.get('/leaderboard', (req, res) => {
    res.json(leaderboardSnapshots);
});

app.post('/spawn', (req, res) => {
    const spawnPoints = req.body.spawnPoints;
    const selectedSpawn = randomSpawn(spawnPoints);
    res.json(selectedSpawn);
});

app.listen(3000, () => {
    console.log('Server is running on port 3000');
    startCountdown();
});
