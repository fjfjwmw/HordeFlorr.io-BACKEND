// Updates made to fix critical bugs in server.js

// Ensuring leaderboard is included in snapshot broadcasts
function broadcastSnapshot() {
    // ... existing logic
    const snapshot = { /* existing snapshot data */ , leaderboard: getLeaderboard() };
    broadcast(snapshot);
}

// Fixing random spawn fallback logic
function spawnEntity() {
    let attempts = 0;
    const maxAttempts = 10; // Additional fallback attempts
    while (attempts < maxAttempts) {
        // ... existing spawn logic with reduced margin
        if (spawnSuccessful) { 
            return;
        }
        attempts++;
        // Log failure
        console.log('Spawn attempt failed, trying again...');
    }
    console.error('Spawn failed after multiple attempts.');
}

// Ensure broadcastQueueUpdate happens before countdown starts
function startCountdown() {
    broadcastQueueUpdate();
    // ... existing countdown logic
}

// Improved spawn failure logging
function logSpawnFailure(details) {
    console.error(`Spawn failed: ${JSON.stringify(details)}`);
}