import init, { compute_syz } from './pkg/m2_port.js';

let wasmReady = false;

async function initWasm() {
    await init();
    wasmReady = true;
}

initWasm().catch(e => {
    console.error('WASM init failed:', e);
    document.getElementById('error-box').textContent = 'Failed to load WASM module: ' + e;
    document.getElementById('error-box').style.display = 'block';
    document.getElementById('output-section').style.display = 'block';
});

// Build the matrix input grid.
function rebuildGrid() {
    const nrows = parseInt(document.getElementById('nrows').value) || 1;
    const ncols = parseInt(document.getElementById('ncols').value) || 1;
    const container = document.getElementById('matrix-container');

    // Save existing values.
    const oldInputs = container.querySelectorAll('input');
    const oldValues = {};
    oldInputs.forEach(input => {
        oldValues[input.dataset.pos] = input.value;
    });

    container.innerHTML = '';
    const grid = document.createElement('div');
    grid.className = 'matrix-grid';
    grid.style.gridTemplateColumns = `repeat(${ncols}, 120px)`;

    for (let i = 0; i < nrows; i++) {
        for (let j = 0; j < ncols; j++) {
            const input = document.createElement('input');
            input.type = 'text';
            input.dataset.pos = `${i},${j}`;
            input.placeholder = '0';
            const key = `${i},${j}`;
            if (oldValues[key]) {
                input.value = oldValues[key];
            }
            grid.appendChild(input);
        }
    }

    container.appendChild(grid);
}

// Compute syz(M).
function compute() {
    if (!wasmReady) {
        alert('WASM module not loaded yet. Please wait.');
        return;
    }

    const vars = document.getElementById('vars').value.trim();
    const nrows = parseInt(document.getElementById('nrows').value) || 1;
    const ncols = parseInt(document.getElementById('ncols').value) || 1;

    // Gather entries.
    const inputs = document.getElementById('matrix-container').querySelectorAll('input');
    const entries = [];
    inputs.forEach(input => {
        entries.push(input.value.trim() || '0');
    });

    const entriesStr = entries.join(';');

    const btn = document.getElementById('compute-btn');
    btn.disabled = true;
    btn.textContent = 'Computing...';

    // Run in a timeout to let the UI update.
    setTimeout(() => {
        try {
            const resultStr = compute_syz(vars, nrows, ncols, entriesStr);
            const result = JSON.parse(resultStr);
            displayResult(result, nrows, ncols);
        } catch (e) {
            displayError('Computation error: ' + e);
        } finally {
            btn.disabled = false;
            btn.textContent = 'Compute syz(M)';
        }
    }, 10);
}

function displayResult(result, nrows, ncols) {
    const outputSection = document.getElementById('output-section');
    const errorBox = document.getElementById('error-box');
    const gbOutput = document.getElementById('gb-output');
    const syzOutput = document.getElementById('syz-output');

    outputSection.style.display = 'block';

    if (result.error) {
        errorBox.textContent = result.error;
        errorBox.style.display = 'block';
        gbOutput.style.display = 'none';
        syzOutput.style.display = 'none';
        return;
    }

    errorBox.style.display = 'none';

    // Display GB.
    if (result.gb && result.gb.length > 0) {
        gbOutput.style.display = 'block';
        const gbLines = result.gb.map((p, i) => `  g${i} = ${p}`);
        document.getElementById('gb-content').textContent = gbLines.join('\n');
    } else {
        gbOutput.style.display = 'none';
    }

    // Display syzygies.
    if (result.nsyz > 0) {
        syzOutput.style.display = 'block';
        const ngens = result.ngens;
        const nsyz = result.nsyz;

        let lines = [];
        lines.push(`${ngens} generators, ${nsyz} syzygy${nsyz === 1 ? '' : 'ies'}`);
        lines.push('');

        // Display as matrix columns.
        for (let k = 0; k < nsyz; k++) {
            lines.push(`Syzygy ${k + 1}:`);
            for (let i = 0; i < ngens; i++) {
                const entry = result.syz[i][k];
                lines.push(`  [${i}] = ${entry}`);
            }
            if (k < nsyz - 1) lines.push('');
        }

        document.getElementById('syz-content').textContent = lines.join('\n');
    } else {
        syzOutput.style.display = 'block';
        document.getElementById('syz-content').textContent = 'No syzygies (kernel is zero).';
    }
}

function displayError(msg) {
    const outputSection = document.getElementById('output-section');
    const errorBox = document.getElementById('error-box');
    outputSection.style.display = 'block';
    errorBox.textContent = msg;
    errorBox.style.display = 'block';
    document.getElementById('gb-output').style.display = 'none';
    document.getElementById('syz-output').style.display = 'none';
}

// Example presets.
const EXAMPLES = {
    monomial: {
        vars: 'x, y',
        nrows: 1,
        ncols: 3,
        entries: ['x^2', 'x*y', 'y^2'],
    },
    twisted: {
        vars: 'x, y, z',
        nrows: 1,
        ncols: 3,
        entries: ['x^2 - y*z', 'x*y - z^2', 'y^2 - x*z'],
    },
    coeff: {
        vars: 'x, y',
        nrows: 1,
        ncols: 2,
        entries: ['3*x + y', '2*x - y'],
    },
    matrix2x2: {
        vars: 'x, y',
        nrows: 2,
        ncols: 2,
        entries: ['x', 'y', 'y', 'x'],
    },
    katsura: {
        vars: 'x, y, z',
        nrows: 1,
        ncols: 2,
        entries: ['x + y + z - 1', 'x^2 + y^2 + z^2 - 1'],
    },
};

function loadExample(name) {
    const ex = EXAMPLES[name];
    if (!ex) return;

    document.getElementById('vars').value = ex.vars;
    document.getElementById('nrows').value = ex.nrows;
    document.getElementById('ncols').value = ex.ncols;
    rebuildGrid();

    const inputs = document.getElementById('matrix-container').querySelectorAll('input');
    ex.entries.forEach((val, i) => {
        if (inputs[i]) inputs[i].value = val;
    });
}

// Initialize grid on load.
rebuildGrid();

// Expose functions to global scope for onclick handlers.
window.rebuildGrid = rebuildGrid;
window.compute = compute;
window.loadExample = loadExample;
