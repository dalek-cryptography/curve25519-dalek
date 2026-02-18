// Update last updated date
document.addEventListener('DOMContentLoaded', function() {
    const lastUpdatedElement = document.getElementById('last-updated');
    if (lastUpdatedElement) {
        const today = new Date();
        const options = { year: 'numeric', month: 'long', day: 'numeric' };
        lastUpdatedElement.textContent = today.toLocaleDateString('en-US', options);
    }

    // Image zoom functionality
    const modal = document.getElementById('imageModal');
    const modalImg = document.getElementById('modalImage');
    const modalCaption = document.getElementById('modalCaption');
    const closeBtn = document.querySelector('.modal-close');
    
    // Add click handlers to all zoomable images
    document.querySelectorAll('.zoomable').forEach(img => {
        img.addEventListener('click', function() {
            modal.classList.add('active');
            modalImg.src = this.src;
            modalCaption.textContent = this.getAttribute('data-title') || this.alt;
        });
    });
    
    // Close modal when clicking the X
    if (closeBtn) {
        closeBtn.addEventListener('click', function() {
            modal.classList.remove('active');
        });
    }
    
    // Close modal when clicking outside the image
    modal.addEventListener('click', function(e) {
        if (e.target === modal) {
            modal.classList.remove('active');
        }
    });
    
    // Close modal with Escape key
    document.addEventListener('keydown', function(e) {
        if (e.key === 'Escape' && modal.classList.contains('active')) {
            modal.classList.remove('active');
        }
    });

    // Navigation items — declared early so anchor-click handler below can use them
    const sections = document.querySelectorAll('section[id]');
    const navItems = document.querySelectorAll('.nav-links a');

    // Smooth scroll for anchor links
    document.querySelectorAll('a[href^="#"]').forEach(anchor => {
        anchor.addEventListener('click', function (e) {
            e.preventDefault();
            const href = this.getAttribute('href');
            const target = document.querySelector(href);
            if (target) {
                // Immediately highlight the clicked link
                navItems.forEach(item => item.classList.remove('active'));
                this.classList.add('active');
                // Update URL hash without jumping
                history.pushState(null, '', href);
                target.scrollIntoView({
                    behavior: 'smooth',
                    block: 'start'
                });
            }
        });
    });

    // Add fade-in animation on scroll
    const observerOptions = {
        threshold: 0.1,
        rootMargin: '0px 0px -50px 0px'
    };

    const observer = new IntersectionObserver((entries) => {
        entries.forEach(entry => {
            if (entry.isIntersecting) {
                entry.target.style.opacity = '1';
                entry.target.style.transform = 'translateY(0)';
            }
        });
    }, observerOptions);

    // Observe all chart cards and content cards
    document.querySelectorAll('.chart-card, .content-card, .trust-item').forEach(el => {
        el.style.opacity = '0';
        el.style.transform = 'translateY(20px)';
        el.style.transition = 'opacity 0.6s ease, transform 0.6s ease';
        observer.observe(el);
    });

    // Mobile menu toggle (if needed in future)
    const navToggle = document.querySelector('.nav-toggle');
    const navLinks = document.querySelector('.nav-links');
    
    if (navToggle) {
        navToggle.addEventListener('click', () => {
            navLinks.classList.toggle('active');
        });
    }

    // Add active state to nav links based on scroll position

    function highlightNavigation() {
        const scrollY = window.pageYOffset;

        sections.forEach(section => {
            const sectionHeight = section.offsetHeight;
            const sectionTop = section.offsetTop - 100;
            const sectionId = section.getAttribute('id');
            
            if (scrollY > sectionTop && scrollY <= sectionTop + sectionHeight) {
                navItems.forEach(item => {
                    item.classList.remove('active');
                    if (item.getAttribute('href') === `#${sectionId}`) {
                        item.classList.add('active');
                    }
                });
            }
        });
    }

    window.addEventListener('scroll', highlightNavigation);
    highlightNavigation(); // highlight on initial load

    // CSV Modal functionality
    let csvFunctionsData = [];
    let currentCsvFilter = 'all';
    const csvModal = document.getElementById('csvModal');
    const csvPreviewTrigger = document.querySelector('.csv-preview-trigger');

    // Open CSV modal when clicking the preview image
    if (csvPreviewTrigger) {
        csvPreviewTrigger.addEventListener('click', () => {
            csvModal.style.display = 'block';
            if (csvFunctionsData.length === 0) {
                loadCsvData();
            }
        });
    }

    // Close CSV modal
    const csvModalClose = document.querySelector('.csv-modal-close');
    if (csvModalClose) {
        csvModalClose.addEventListener('click', () => {
            csvModal.style.display = 'none';
        });
    }

    // Close modal when clicking outside
    window.addEventListener('click', (event) => {
        if (event.target === csvModal) {
            csvModal.style.display = 'none';
        }
    });

    // Close modal with Escape key
    document.addEventListener('keydown', (event) => {
        if (event.key === 'Escape' && csvModal.style.display === 'block') {
            csvModal.style.display = 'none';
        }
    });

    // Load and parse CSV
    async function loadCsvData() {
        try {
            const response = await fetch('outputs/curve25519_functions.csv');
            const csvText = await response.text();
            
            // Parse CSV (handles quoted fields with commas)
            function parseCSVLine(line) {
                const result = [];
                let current = '';
                let inQuotes = false;
                
                for (let i = 0; i < line.length; i++) {
                    const char = line[i];
                    if (char === '"') {
                        inQuotes = !inQuotes;
                    } else if (char === ',' && !inQuotes) {
                        result.push(current.trim());
                        current = '';
                    } else {
                        current += char;
                    }
                }
                result.push(current.trim());
                return result;
            }
            
            const lines = csvText.trim().split('\n');
            const headers = parseCSVLine(lines[0]);
            
            csvFunctionsData = lines.slice(1).map(line => {
                const values = parseCSVLine(line);
                const func = {};
                headers.forEach((header, i) => {
                    func[header] = values[i] || '';
                });
                return func;
            });
            
            renderCsvTable();
        } catch (error) {
            console.error('Error loading CSV:', error);
            document.getElementById('csvTableBody').innerHTML = 
                '<tr><td colspan="5" class="loading">Error loading data</td></tr>';
        }
    }

    function extractModule(link) {
        if (!link) return 'unknown';
        if (link.includes('.rs#')) {
            const match = link.split('.rs#')[0];
            if (match.includes('/')) {
                return match.split('/').pop() + '.rs';
            }
        }
        return 'unknown';
    }

    function getStatus(func) {
        if (func.has_proof === 'yes') {
            return { class: 'verified', text: '✓ Verified' };
        } else if (func.has_spec === 'ext') {
            return { class: 'external', text: '⊕ External' };
        } else if (func.has_spec === 'yes') {
            return { class: 'spec', text: '○ Spec Only' };
        } else {
            return { class: 'none', text: '· No Spec' };
        }
    }

    function renderCsvTable() {
        const tbody = document.getElementById('csvTableBody');
        const searchBox = document.getElementById('csvSearch');
        const searchTerm = searchBox ? searchBox.value.toLowerCase() : '';
        
        let filteredFunctions = csvFunctionsData.filter(func => {
            // Apply search filter
            const matchesSearch = !searchTerm || 
                func.function.toLowerCase().includes(searchTerm) ||
                func.module.toLowerCase().includes(searchTerm);
            
            if (!matchesSearch) return false;
            
            // Apply status filter
            if (currentCsvFilter === 'all') return true;
            if (currentCsvFilter === 'verified') return func.has_proof === 'yes';
            if (currentCsvFilter === 'spec') return func.has_spec === 'yes' || func.has_spec === 'ext';
            if (currentCsvFilter === 'external') return func.has_spec === 'ext';
            if (currentCsvFilter === 'none') return !func.has_spec && !func.has_proof;
            
            return true;
        });
        
        if (filteredFunctions.length === 0) {
            tbody.innerHTML = '<tr><td colspan="5" class="loading">No functions match your filters</td></tr>';
            return;
        }
        
        tbody.innerHTML = filteredFunctions.map(func => {
            const status = getStatus(func);
            // Use module from CSV, but shorten it for display (last 2 parts)
            let displayModule = func.module;
            if (displayModule.includes('::')) {
                const parts = displayModule.split('::');
                displayModule = parts.slice(-2).join('::');
            }
            
            return `
                <tr>
                    <td class="function-name">${func.function}</td>
                    <td class="function-module">${displayModule}</td>
                    <td><span class="status-badge status-${status.class}">${status.text}</span></td>
                    <td><a href="${func.link}" target="_blank" class="function-link">View Source →</a></td>
                    <td><a href="https://beneficial-ai-foundation.github.io/dalek-lite/callgraph/?source=${encodeURIComponent(func.function.replace(/\(.*$/, ''))}&sink=${encodeURIComponent(func.function.replace(/\(.*$/, ''))}" target="_blank" class="function-link">Graph →</a></td>
                </tr>
            `;
        }).join('');
    }

    // Search functionality for CSV modal
    const csvSearchBox = document.getElementById('csvSearch');
    if (csvSearchBox) {
        csvSearchBox.addEventListener('input', renderCsvTable);
    }

    // Filter functionality for CSV modal
    const csvFilterButtons = document.querySelectorAll('#csvModal .filter-btn');
    csvFilterButtons.forEach(btn => {
        btn.addEventListener('click', () => {
            csvFilterButtons.forEach(b => b.classList.remove('active'));
            btn.classList.add('active');
            currentCsvFilter = btn.getAttribute('data-filter');
            renderCsvTable();
        });
    });

    // Load and display time period metadata
    async function loadTimePeriod() {
        try {
            const response = await fetch('outputs/metadata.json');
            const metadata = await response.json();
            
            // Format dates as "Oct 21 - Oct 28"
            const firstDate = new Date(metadata.first_date);
            const lastDate = new Date(metadata.last_date);
            
            const formatDate = (date) => {
                return date.toLocaleDateString('en-US', { month: 'short', day: 'numeric' });
            };
            
            const timePeriodText = `${formatDate(firstDate)} - ${formatDate(lastDate)}`;
            const daysText = `${metadata.total_days} days of tracking data`;
            
            document.getElementById('timePeriod').textContent = timePeriodText;
            document.getElementById('timePeriodDays').textContent = daysText;
        } catch (error) {
            console.error('Error loading time period:', error);
            // Fallback text
            document.getElementById('timePeriod').textContent = 'Recent data';
            document.getElementById('timePeriodDays').textContent = 'Tracking period';
        }
    }
    
    // Load stats from JSON
    async function loadStats() {
        try {
            const response = await fetch('outputs/stats.json');
            const stats = await response.json();
            
            // Update hero stats
            document.getElementById('withSpecs').textContent = stats.with_specs;
            document.getElementById('fullyVerified').textContent = stats.fully_verified;
            document.getElementById('fullyVerifiedPct').textContent = `${stats.proof_completion_rate}%`;
            
            // Update metrics section
            document.getElementById('specCompletionRate').textContent = `${stats.with_specs_pct}%`;
            document.getElementById('specCompletionDesc').textContent = 
                `${stats.with_specs} of ${stats.total_functions} functions have specs`;
            document.getElementById('proofCompletionRate').textContent = `${stats.proof_completion_rate}%`;
            document.getElementById('proofCompletionDesc').textContent = 
                `${stats.fully_verified} of ${stats.with_specs} specs are fully proven`;
            
            // Update CSV preview and modal totals
            document.getElementById('csvPreviewTotal').textContent = stats.total_functions;
            document.getElementById('csvModalTotal').textContent = stats.total_functions;
        } catch (error) {
            console.error('Error loading stats:', error);
            // Keep fallback values that are hardcoded in HTML
        }
    }
    
    // Load certifications history
    async function loadCertifications() {
        try {
            // Fetch from certifications-data branch (avoids protected main branch)
            // Falls back to local path for development
            const CERTIFICATIONS_URL = 'https://raw.githubusercontent.com/Beneficial-AI-Foundation/dalek-lite/certifications-data/certifications.json';
            
            let response;
            try {
                response = await fetch(CERTIFICATIONS_URL);
                if (!response.ok) throw new Error('Remote fetch failed');
            } catch (e) {
                // Fallback for local development
                console.log('Falling back to local certifications.json');
                response = await fetch('certifications.json');
            }
            const data = await response.json();
            
            const tbody = document.getElementById('certificationsTableBody');
            const description = document.getElementById('certificationsDescription');
            
            if (!data.certifications || data.certifications.length === 0) {
                tbody.innerHTML = `
                    <tr>
                        <td colspan="8" class="certifications-empty">
                            No certifications recorded yet. Certifications will appear here after verification runs.
                        </td>
                    </tr>
                `;
                description.innerHTML = '<em>Certifications will be recorded automatically on each verification run.</em>';
                return;
            }
            
            // Escape HTML special characters to prevent XSS
            const escapeHtml = (str) => {
                if (!str) return '';
                const div = document.createElement('div');
                div.textContent = String(str);
                return div.innerHTML;
            };
            
            // Validate URL matches expected patterns
            const isValidEtherscanUrl = (url) => {
                if (!url) return false;
                return /^https:\/\/(sepolia\.)?etherscan\.io\/tx\/0x[a-fA-F0-9]{64}$/.test(url);
            };
            
            const isValidGitHubUrl = (url) => {
                if (!url) return false;
                // Disallow consecutive dots and trailing dots in owner/repo; require alpha/underscore start; constrain final segment
                return /^https:\/\/github\.com\/(?!.*\.\.)[a-zA-Z_](?:[\w.-]*[\w])?\/[a-zA-Z_](?:[\w.-]*[\w])?\/(commit|actions\/runs)\/(?:[0-9a-fA-F]{40}|\d+)$/.test(url);
            };
            
            const isValidHex = (str) => {
                if (!str) return false;
                return /^(0x)?[a-fA-F0-9]+$/.test(str);
            };
            
            // Format date and time nicely
            const formatDateTime = (isoDate) => {
                if (!isoDate) return '—';
                const date = new Date(isoDate);
                // Check if date is valid
                if (isNaN(date.getTime())) {
                    return '—';
                }
                return date.toLocaleString('en-US', { 
                    month: 'short', 
                    day: 'numeric',
                    year: 'numeric',
                    hour: '2-digit',
                    minute: '2-digit'
                });
            };
            
            // Truncate hash for display
            const truncateHash = (hash) => {
                if (!hash) return '';
                
                const hashStr = String(hash);
                
                // If the hash is too short to meaningfully truncate (10 + 6),
                // return it as-is to avoid overlapping or duplicated segments.
                if (hashStr.length <= 16) {
                    return escapeHtml(hashStr);
                }
                
                return escapeHtml(hashStr.slice(0, 10) + '...' + hashStr.slice(-6));
            };
            
            tbody.innerHTML = data.certifications.map(cert => {
                // Validate and sanitize URLs before use
                const mainnetLink = (cert.mainnet_etherscan && isValidEtherscanUrl(cert.mainnet_etherscan))
                    ? `<a href="${escapeHtml(cert.mainnet_etherscan)}" target="_blank" rel="noopener noreferrer" class="tx-link">View ↗</a>`
                    : '<span class="no-data">—</span>';
                    
                const sepoliaLink = (cert.sepolia_etherscan && isValidEtherscanUrl(cert.sepolia_etherscan))
                    ? `<a href="${escapeHtml(cert.sepolia_etherscan)}" target="_blank" rel="noopener noreferrer" class="tx-link">View ↗</a>`
                    : '<span class="no-data">—</span>';
                
                // Validate commit SHA is hex before constructing URL
                const commitSha = isValidHex(cert.commit_sha) ? String(cert.commit_sha).toLowerCase() : '';
                const commitShort = escapeHtml(cert.commit_short || '');
                const commitLink = commitSha
                    ? `<a href="https://github.com/Beneficial-AI-Foundation/dalek-lite/commit/${commitSha}" target="_blank" rel="noopener noreferrer" class="commit-link">${commitShort}</a>`
                    : `<span class="no-data">${commitShort || '—'}</span>`;
                
                const artifactLink = (cert.artifact_url && isValidGitHubUrl(cert.artifact_url))
                    ? `<a href="${escapeHtml(cert.artifact_url)}" target="_blank" rel="noopener noreferrer" class="artifact-link">Download ↗</a>`
                    : '<span class="no-data">—</span>';
                
                // Validate content hash is hex
                const safeContentHash = isValidHex(cert.content_hash) ? escapeHtml(cert.content_hash) : '';
                const contentHashDisplay = safeContentHash
                    ? `<span class="content-hash" title="${safeContentHash}">${truncateHash(cert.content_hash)}</span>`
                    : '<span class="no-data">—</span>';
                
                // Validate numeric values
                const verifiedCount = Number.isInteger(cert.verified_count) ? cert.verified_count : null;
                const totalFunctions = Number.isInteger(cert.total_functions) ? cert.total_functions : null;
                const verifiedDisplay = (verifiedCount !== null && totalFunctions !== null)
                    ? `<span class="verified-count">${verifiedCount}</span>/${totalFunctions}`
                    : '<span class="no-data">—</span>';
                
                // Display Verus version (sanitized)
                const verusVersion = cert.verus_version ? escapeHtml(cert.verus_version) : '';
                const verusDisplay = verusVersion
                    ? `<span class="verus-version" title="${verusVersion}">${verusVersion}</span>`
                    : '<span class="no-data">—</span>';
                
                return `
                    <tr>
                        <td>${formatDateTime(cert.timestamp)}</td>
                        <td>${commitLink}</td>
                        <td>${verusDisplay}</td>
                        <td>${verifiedDisplay}</td>
                        <td>${contentHashDisplay}</td>
                        <td>${mainnetLink}</td>
                        <td>${sepoliaLink}</td>
                        <td>${artifactLink}</td>
                    </tr>
                `;
            }).join('');
            
            const totalCerts = data.certifications.length;
            const latestCert = data.certifications[0];
            const latestCommitSha = isValidHex(latestCert.commit_sha) ? String(latestCert.commit_sha) : '';
            const latestCommitShort = escapeHtml(latestCert.commit_short || '');
            const latestCommitLink = latestCommitSha
                ? `<a href="https://github.com/Beneficial-AI-Foundation/dalek-lite/commit/${latestCommitSha}" target="_blank" rel="noopener noreferrer">${latestCommitShort}</a>`
                : latestCommitShort;
            description.innerHTML = `
                <strong>${totalCerts} certification${totalCerts === 1 ? '' : 's'}</strong> recorded. 
                Latest: ${formatDateTime(latestCert.timestamp)} 
                (${latestCommitLink})
            `;
            
        } catch (error) {
            console.error('Error loading certifications:', error);
            const tbody = document.getElementById('certificationsTableBody');
            tbody.innerHTML = `
                <tr>
                    <td colspan="8" class="certifications-empty">
                        Unable to load certifications. They will appear here after the first verification run.
                    </td>
                </tr>
            `;
            document.getElementById('certificationsDescription').innerHTML = 
                '<em>Certifications will be recorded automatically on each verification run.</em>';
        }
    }
    
    // Load time period on page load
    loadTimePeriod();
    loadStats();
    loadCertifications();
});

