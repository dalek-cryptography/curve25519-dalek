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

    // Smooth scroll for anchor links
    document.querySelectorAll('a[href^="#"]').forEach(anchor => {
        anchor.addEventListener('click', function (e) {
            e.preventDefault();
            const target = document.querySelector(this.getAttribute('href'));
            if (target) {
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
    const sections = document.querySelectorAll('section[id]');
    const navItems = document.querySelectorAll('.nav-links a');

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

    // Function browser functionality
    let functionsData = [];
    let currentFilter = 'all';

    // Load and parse CSV
    async function loadFunctions() {
        try {
            const response = await fetch('../outputs/curve25519_functions.csv');
            const csvText = await response.text();
            
            // Parse CSV
            const lines = csvText.trim().split('\n');
            const headers = lines[0].split(',');
            
            functionsData = lines.slice(1).map(line => {
                const values = line.split(',');
                const func = {};
                headers.forEach((header, i) => {
                    func[header.trim()] = values[i] ? values[i].trim() : '';
                });
                return func;
            });
            
            renderFunctions();
        } catch (error) {
            console.error('Error loading functions:', error);
            document.getElementById('functionTableBody').innerHTML = 
                '<tr><td colspan="4" class="loading">Error loading functions data</td></tr>';
        }
    }

    function extractModule(link) {
        if (!link) return 'unknown';
        const match = link.match(/\/([^\/]+\.rs)#/);
        return match ? match[1] : 'unknown';
    }

    function getStatus(func) {
        if (func.has_proof_verus === 'yes') {
            return { class: 'verified', text: 'Verified' };
        } else if (func.has_spec_verus === 'ext') {
            return { class: 'external', text: 'External' };
        } else if (func.has_spec_verus === 'yes') {
            return { class: 'spec', text: 'Spec Only' };
        } else {
            return { class: 'none', text: 'No Spec' };
        }
    }

    function renderFunctions() {
        const tbody = document.getElementById('functionTableBody');
        const searchTerm = document.getElementById('functionSearch').value.toLowerCase();
        
        let filteredFunctions = functionsData.filter(func => {
            // Apply search filter
            const matchesSearch = !searchTerm || 
                func.function_name.toLowerCase().includes(searchTerm) ||
                extractModule(func.link).toLowerCase().includes(searchTerm);
            
            if (!matchesSearch) return false;
            
            // Apply status filter
            if (currentFilter === 'all') return true;
            if (currentFilter === 'verified') return func.has_proof_verus === 'yes';
            if (currentFilter === 'spec') return func.has_spec_verus === 'yes' || func.has_spec_verus === 'ext';
            if (currentFilter === 'none') return !func.has_spec_verus && !func.has_proof_verus;
            
            return true;
        });
        
        if (filteredFunctions.length === 0) {
            tbody.innerHTML = '<tr><td colspan="4" class="loading">No functions match your filters</td></tr>';
            return;
        }
        
        tbody.innerHTML = filteredFunctions.map(func => {
            const status = getStatus(func);
            const module = extractModule(func.link);
            
            return `
                <tr>
                    <td class="function-name">${func.function_name}</td>
                    <td class="function-module">${module}</td>
                    <td><span class="status-badge status-${status.class}">${status.text}</span></td>
                    <td><a href="${func.link}" target="_blank" class="function-link">View Source →</a></td>
                </tr>
            `;
        }).join('');
    }

    // Search functionality
    const searchBox = document.getElementById('functionSearch');
    if (searchBox) {
        searchBox.addEventListener('input', renderFunctions);
    }

    // Filter functionality
    const filterButtons = document.querySelectorAll('.filter-btn');
    filterButtons.forEach(btn => {
        btn.addEventListener('click', () => {
            filterButtons.forEach(b => b.classList.remove('active'));
            btn.classList.add('active');
            currentFilter = btn.getAttribute('data-filter');
            renderFunctions();
        });
    });

    // Load functions on page load
    if (document.getElementById('functionTable')) {
        loadFunctions();
    }
});

