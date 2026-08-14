import { Readline } from 'xterm-readline';

const arity = document.getElementById("arity");
const direction = document.getElementById("direction");
const internal = document.getElementById("internal");
const external = document.getElementById("external");
const startup = document.getElementById("startup");

const queryString = window.location.search;
const urlParams = new URLSearchParams(queryString);
if(urlParams.has('arity')) {
    arity.value = urlParams.get('arity');
}
if(urlParams.has('direction')) {
    direction.value = urlParams.get('direction');
}
if(urlParams.has('internal')) {
    internal.checked = true;
}
if(urlParams.has('external')) {
    external.checked = true;
}
if(urlParams.has('startup')) {
    startup.value = urlParams.get('startup');
}
if(urlParams.has('dtt')) {
    arity.value = 1;
    direction.value = 'd';
    external.checked = true;
}

const term = new Terminal({
    cursorBlink: true,
    fontSize: 20,
    rows: 30
});
term.open(document.getElementById('terminal'));
const rl = new Readline();
term.loadAddon(rl);

rl.setCheckHandler((text) => {
    if (text.endsWith("\n")) {
        return true;
    }
    return false;
});

function readLine() {
    term.write("\x1B[4mnarya\x1B[0m\n\r");
    rl.read("").then(processLine);
}

function processLine(text) {
    rl.println(Narya.execute(text));
    setTimeout(readLine);
}

function start() {
    term.clear();

    var startupcode = startup.value
    
    var err = Narya.start(arity.value, direction.value, internal.checked, startupcode);
    if (!err) {
        arity.disabled = true;
        direction.disabled = true;
        internal.disabled = true;
        external.disabled = true;
        startup.disabled = true;
        readLine();
        term.focus();
    } else {
        rl.println("\n" + err + "Please fix the error and reload the page.");
    }
}

document.getElementById("start").addEventListener('click', start);

function insert(str) {
    term.input(str);
    term.focus();
}

const palette = document.getElementById('palette');

function addToPalette(str) {
    var b = document.createElement('button');
    b.textContent = str;
    b.style = "font-size:1.2em";
    b.addEventListener('click', function() { insert(str) });
    palette.appendChild(b);
}

const characters = ['→', '↦', '⤇', '≔', '…', '⁽', '⁾', '⁰', '¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹', 'ᵃ', 'ᵇ', 'ᶜ', 'ᵈ', 'ᵉ', 'ᶠ', 'ᵍ', 'ʰ', 'ⁱ', 'ʲ', 'ᵏ', 'ˡ', 'ᵐ', 'ⁿ', 'ᵒ', 'ᵖ', '𐞥', 'ʳ', 'ˢ', 'ᵗ', 'ᵘ', 'ᵛ', 'ʷ', 'ˣ', 'ʸ', 'ᶻ', '₀', '₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉', '×', '⊔', '⊎', '♯', '♭', '♮', 'ℂ', 'ℕ', 'ℝ', 'ℤ', '⟨', '⟩', '⟦', '⟧', '≡', '≤', '≥', '≠', 'α', 'β', 'γ', 'δ', 'ε', 'ζ', 'η', 'θ', 'ι', 'κ', 'λ', 'μ', 'ν', 'ξ', 'ο', 'π', 'ρ', 'σ', 'τ', 'υ', 'φ', 'χ', 'ψ', 'ω', 'Γ', 'Δ', 'Θ', 'Λ', 'Ξ', 'Π', 'Σ', 'Φ', 'Ψ', 'Ω', '∀', '∃', '∧', '∨', '¬', '⊤', '⊥'];
characters.forEach(addToPalette);
