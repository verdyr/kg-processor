package org.verdyr.semantics.processor;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Date;
import java.util.GregorianCalendar;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Properties;
import java.util.concurrent.ScheduledThreadPoolExecutor;
import java.util.concurrent.TimeUnit;

import javax.xml.datatype.DatatypeConfigurationException;
import javax.xml.datatype.DatatypeFactory;
import javax.xml.datatype.XMLGregorianCalendar;

import org.apache.commons.lang3.StringUtils;
import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.ModelFactory;
import org.apache.jena.rdf.model.RDFNode;
import org.apache.jena.rdf.model.StmtIterator;
import org.jutils.jprocesses.JProcesses;
import org.jutils.jprocesses.model.ProcessInfo;
import org.openrdf.model.Graph;
import org.openrdf.model.Statement;
import org.openrdf.model.URI;
import org.openrdf.model.Value;
import org.openrdf.model.impl.LinkedHashModel;
import org.openrdf.model.impl.URIImpl;
import org.openrdf.model.impl.ValueFactoryImpl;
import org.openrdf.query.Binding;
import org.openrdf.query.BindingSet;
import org.openrdf.query.QueryLanguage;
import org.openrdf.query.TupleQueryResult;
import org.openrdf.query.Update;
import org.openrdf.rio.RDFFormat;
import org.openrdf.rio.RDFHandlerException;
import org.openrdf.rio.RDFParseException;
import org.openrdf.rio.RDFWriter;
import org.openrdf.rio.RDFWriterFactory;
import org.openrdf.rio.RDFWriterRegistry;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.concurrent.ConcurrentHashMap;
import java.util.HashMap;
import com.bigdata.journal.BufferMode;
import com.bigdata.journal.Options;
import com.mapr.db.MapRDB;
import com.mapr.db.Table;

import com.pwc.df.semantics.helper.MaprDBHelper;
import org.ojai.Document;
import org.ojai.DocumentStream;
import org.ojai.store.DocumentMutation;
import org.ojai.store.QueryCondition;


import com.bigdata.rdf.axioms.NoAxioms;
import com.bigdata.rdf.sail.BigdataSail;
import com.bigdata.rdf.sail.remote.BigdataSailRemoteRepository;
import com.bigdata.rdf.sail.remote.BigdataSailRemoteRepositoryConnection;
import com.bigdata.rdf.sail.webapp.NanoSparqlServer;
import com.bigdata.rdf.sail.webapp.client.ConnectOptions;
import com.bigdata.rdf.sail.webapp.client.JettyResponseListener;
import com.bigdata.rdf.sail.webapp.client.RemoteRepository;
import com.bigdata.rdf.sail.webapp.client.RemoteRepository.AddOp;
import com.bigdata.rdf.sail.webapp.client.RemoteRepositoryManager;
import com.bigdata.rdf.store.AbstractTripleStore.Options;
import com.bigdata.rwstore.RWStore;

import osee.TempFolderCreator;
import processor.AdfReader;
import processor.util.RdfUtil;
import processor.util.RunUtil;

import javax.enterprise.context.control.ActivateRequestContext;
import javax.inject.Inject;

import io.quarkus.runtime.Quarkus;
import io.quarkus.runtime.QuarkusApplication;
import io.quarkus.runtime.annotations.QuarkusMain;

//@QuarkusMain
//public class TripleStore implements QuarkusApplication {


/*
*   SB
*   adapted from Adf Server for GDPR graph test, as a MapRDB Table OJAI reader, with and w/o NER
*/


public class BlazegraphTripleStore extends NanoSparqlServer
{

     public static final String JOURNAL_FILE_NAME = TempFolderCreator.TRIPLE_STORE_FOLDER_PATH_NAME + "blazegraph.jnl";

     private static final URI MERGED = new URIImpl("http://localhost/blazegraph/merged");

     private static final URI INSTANCES = new URIImpl("http://localhost/blazegraph/instances");

     private static final URI VOCABULARY = new URIImpl("http://localhost/blazegraph/vocabulary");

     public static Logger logger = LoggerFactory.getLogger("log");

     private static final String sparqlEndPoint = "http://localhost:9999/blazegraph";

     private static final String datasetName = "gdpr";

     public static void initializeTripleStore()
     {
        final RemoteRepositoryManager repomanager = new RemoteRepositoryManager(sparqlEndPoint, false /* useLBS */);

     	try
     	{
     		JettyResponseListener response = getStatus(repomanager);
     		logger.info(response.getResponseBody());

     		final Properties properties = new Properties();
     		properties.put(BigdataSail.Options.NAMESPACE, datasetName);
     		properties.put(BigdataSail.Options.TRUTH_MAINTENANCE, "false");
     		properties.put(Options.STATEMENT_IDENTIFIERS, "false");
     		properties.put(com.bigdata.journal.Options.BUFFER_MODE, BufferMode.DiskRW);
     		properties.put(Options.AXIOMS_CLASS, NoAxioms.class.getName());
     		properties.put(Options.QUADS, "true");
     		properties.put(com.bigdata.journal.Options.TMP_DIR, TempFolderCreator.TRIPLE_STORE_FOLDER_PATH_NAME);
     		properties.put(com.bigdata.journal.Options.CREATE_TEMP_FILE, "true");
     		properties.put(com.bigdata.journal.Options.DELETE_ON_EXIT, "true");
     		properties.put(com.bigdata.journal.Options.FILE, JOURNAL_FILE_NAME);
     		properties.put(RWStore.Options.READ_BLOBS_ASYNC, "false");

     		repomanager.createRepository(datasetName, properties);
     		logger.info("Created namespace " + datasetName);

     		// turn off entailment
     		// suppressTruthMaintenance(repomanager);

     		// get properties for namespace
     		logger.info("Property list for namespace " + datasetName);
     		response = getNamespaceProperties(repomanager, datasetName);
     		logger.info(response.getResponseBody());

     		// add named graphs
     		createGraph(repomanager, datasetName, VOCABULARY);
     		createGraph(repomanager, datasetName, INSTANCES);
     		createGraph(repomanager, datasetName, MERGED);
     	}
     	catch (Exception e)
     	{
     		logger.info("Error initializing triple store");
     		e.printStackTrace();
     	}
     	finally
     	{
     		closeRepoManager(repomanager);
     	}
     }

     public static void cleanupTripleStore()
     {
     	final RemoteRepositoryManager repomanager = new RemoteRepositoryManager(sparqlEndPoint, false /* useLBS */);

     	try
     	{
     		// logger.info(String.format("Drop all graphs in dataset ", datasetName));
     		// String update = "DROP ALL";
     		// repomanager.getRepositoryForNamespace(datasetName).prepareUpdate(update.toString()).evaluate();

     		logger.info("Clear all graphs in dataset " + datasetName);
     		String update = "CLEAR ALL";
     		repomanager.getRepositoryForNamespace(datasetName).prepareUpdate(update.toString()).evaluate();

     		// clearGraph(repomanager, VOCABULARY);
     		// clearGraph(repomanager, INSTANCES);
     		// clearGraph(repomanager, MERGED);
     	}
     	catch (Exception e)
     	{
     		logger.info("Exception during clearing existing graphs in namespace " + datasetName);
     		e.printStackTrace();
     	}
     	finally
     	{
     		closeRepoManager(repomanager);
     	}
     }

     private static void closeRepoManager(final RemoteRepositoryManager repomanager)
     {
     	try
     	{
     		repomanager.close();
     	}
     	catch (Exception e)
     	{
     		logger.info("Error closing blazegraph repository manager.");
     		e.printStackTrace();
     	}
     }

     public static void loadTriplesInNewThread(Model model, Model externalResources)
     {
     	try
     	{
     		class TriplesLoaderThread extends Thread
     		{
     			private Model model;
     			private Model externalResources;

     			public TriplesLoaderThread(Model model, Model externalResources)
     			{
     				super();
     				this.model = model;
     				this.externalResources = externalResources;
     			}

     			@Override
     			public void run() throws Exception {
     			{
     				BlazegraphTripleStore.loadToTripleStore(model, externalResources);
     			}
     		}

     		TriplesLoaderThread loaderThread = new TriplesLoaderThread(model, externalResources);
     		loaderThread.start();
     	}
     	catch (Exception e)
     	{
     		logger.info("Error during loading triples to triple store.");
     		e.printStackTrace();
     	}

     }

/*
 *   SB
 *   adapted from Adf to load BagOfWords, as a Reader, with and w/o NER
 * 
 */

     public static void loadKgToTripleStore(String tablePath)
     {
        table = MaprDBHelper.getTable(TABLE_NAME);

        // Map init plug replaced with HashMap init
        Map<String, Model> graphMap = new HashMap<>(); // ListMap, to check against RDF serialiasation in BlazeGraph

        DocumentStream rs = table.find();
        Iterator<Document> itrs = rs.iterator();

        Document document;

        while (itrs.hasNext()) {
            document = itrs.next();
            graphMap.add(document.asMap());
        }
        rs.close();

//      	Map<String, Model> graphMap = AdfReader.extractDataDescription(BagOfWordsPath, logger);
     	if (graphMap.isEmpty())
     	{
     		logger.error("No graphs were extracted from BagOgWords: " + tablePath);
     		return;
     	}

     	for (Entry<String, Model> entry : graphMap.entrySet())
     	{
     		String graphName = entry.getKey();
     		Model model = entry.getValue();
     		loadToGraphInNewThread(graphName, model);
     	}
     }

/*
 *
 */


     public static void loadToGraphInNewThread(String graphName, Model model)
     {
     	try
     	{
     		class GraphLoaderThread extends Thread
     		{
     			private Model model;
     			private String graphName;

     			public GraphLoaderThread(String graphName, Model model)
     			{
     				super();
     				this.model = model;
     				this.graphName = graphName;
     			}

     			@Override
     			public void run()
     			{
     				BlazegraphTripleStore.loadToGraph(graphName, model);
     			}
     		}

     		GraphLoaderThread graphLoaderThread = new GraphLoaderThread(graphName, model);
     		logger.info("Loading triples to graph " + graphName + " in thread " + graphLoaderThread.getId());
     		graphLoaderThread.start();
     	}
     	catch (Exception e)
     	{
     		logger.info("Error during loading triples to graph: " + graphName);
     		e.printStackTrace();
     	}

     }

     public static void loadToGraph(String graphName, Model model)
     {
     	logger.info("Loading triples to graph: " + graphName);

     	final RemoteRepositoryManager repomanager = new RemoteRepositoryManager(sparqlEndPoint, false /* useLBS */);

     	URI graphUri = new URIImpl(graphName);
     	try
     	{
     		long numTriples = -1;

     		if (!graphName.equals(RdfUtil.defaultGraph))
     		{
     			if (!namedGraphExists(repomanager, graphUri))
     			{
     				logger.info("Graph " + graphUri + " does not exist. Creating new...");
     				createGraph(repomanager, datasetName, graphUri);
     			}
     			else
     			{
     				logger.info("Graph " + graphUri + " exists. Clearing now...");
     				clearGraph(repomanager, graphUri);
     			}

     			Graph graph = readGraphFromModel(model, graphName);
     			numTriples = doInsertByBody(repomanager, "POST", graph, graphUri);
     			logger.info("Loaded triples to graph " + graphName + " #triples = " + numTriples);
     		}
     		else
     		{
     			loadDataFromModel(repomanager, datasetName, model);
     			numTriples = model.size();
     			logger.info("Loaded triples to default graph #triples = " + numTriples);
     		}

     	}
     	catch (Exception e)
     	{
     		logger.info("Exception during loading triples to graph: " + graphName);
     		e.printStackTrace();
     	}
     	finally
     	{
     		try
     		{
     			repomanager.close();
     		}
     		catch (Exception e)
     		{
     			logger.info("Exception during closing blazegraph repository manager.");
     			e.printStackTrace();
     		}
     	}
     }

     private static void clearGraph(RemoteRepositoryManager repomanager, URI graphUri) throws Exception
     {
     	logger.info("Delete all triples from graph " + graphUri + " in dataset " + datasetName);
     	String update = "DELETE { graph ?g { ?s ?p ?o }} WHERE { graph <" + graphUri + "> { ?s ?p ?o }}";
     	repomanager.getRepositoryForNamespace(datasetName).prepareUpdate(update.toString()).evaluate();
     }

     private static boolean namedGraphExists(RemoteRepositoryManager repomanager, URI graphUri) throws Exception
     {
     	final String queryStr = "select distinct ?g where { graph ?g { ?s ?p ?o } }";
     	TupleQueryResult result = repomanager.getRepositoryForNamespace(datasetName).prepareTupleQuery(queryStr).evaluate();
     	try
     	{
     		while (result.hasNext())
     		{
     			BindingSet bindingSet = result.next();
     			Binding binding = bindingSet.getBinding("g");
     			if (binding == null)
     			{
     				continue;
     			}

     			String value = binding.getValue().stringValue();
     			if (graphUri.equals(value))
     			{
     				return true;
     			}
     		}
     	}
     	finally
     	{
     		result.close();
     	}

     	return false;
     }

     public static void loadToTripleStore(Model model, Model externalResources)
     {
     	logger.info("Loading triples to triple store.");

     	final RemoteRepositoryManager repomanager = new RemoteRepositoryManager(sparqlEndPoint, false /* useLBS */);

     	try
     	{
     		Graph instanceGraph = readGraphFromModel(model, INSTANCES.toString());
     		Graph vocabularyGraph = readGraphFromModel(externalResources, VOCABULARY.toString());

     		long numTriples = doInsertByBody(repomanager, "POST", instanceGraph, INSTANCES);
     		logger.info("Loading instance data to graph " + INSTANCES + " #triples = " + numTriples);

     		numTriples = doInsertByBody(repomanager, "POST", vocabularyGraph, VOCABULARY);
     		logger.info("Loading vocabulary to graph " + VOCABULARY + " #triples = " + numTriples);

     		numTriples = doInsertByBody(repomanager, "POST", instanceGraph, MERGED);
     		logger.info("Loading instance data to graph " + MERGED + " #triples = " + numTriples);

     		numTriples = doInsertByBody(repomanager, "POST", vocabularyGraph, MERGED);
     		logger.info("Loading vocabulary to graph " + MERGED + " #triples = " + numTriples);
     	}
     	catch (Exception e)
     	{
     		logger.info("Exception during loading triples to triple store.");
     		e.printStackTrace();
     	}
     	finally
     	{
     		try
     		{
     			repomanager.close();
     		}
     		catch (Exception e)
     		{
     			logger.info("Exception during closing blazegraph repository manager.");
     			e.printStackTrace();
     		}
     	}
     }

     public void run()
     {
     	if (RunUtil.available(9999))
     	{
     		removeBlazegraphJournal();

     		startUp();
     	}
     	else
     	{
     		logger.info("Blazegraph is already running on port 9999. Trying to stop the orphan process. Please wait...");

     		ProcessInfo blazegraphProcessInfo = RunUtil.getProcessInfo("blazegraph.jar");

     		if (blazegraphProcessInfo != null && StringUtils.isNotEmpty(blazegraphProcessInfo.getPid()))
     		{
     			int pid = Integer.valueOf(blazegraphProcessInfo.getPid());
     			boolean success = JProcesses.killProcessGracefully(pid).isSuccess();
     			if (!success)
     			{
     				logger.info("Could not stop process " + pid + " gracefully.");
     				success = JProcesses.killProcess(pid).isSuccess();
     				if (!success)
     				{
     					logger.info("Could not kill process " + pid);
     					throw new IllegalStateException("Unable to start triple store because there is already a process of Blazegraph running with process ID " + pid);
     				}
     				else
     				{
     					logger.info("Process " + pid + " was killed.");
     				}
     			}
     			else
     			{
     				logger.info("Process " + pid + " was stopped gracefully.");
     			}

     			if (RunUtil.available(9999))
     			{
     				removeBlazegraphJournal();
     				startUp();
     			}
     			else
     			{
     				throw new IllegalStateException("Process with id " + pid + " was stopped but port 9999 is still blocked. Please try a fresh startup.");
     			}
     		}
     		else
     		{
     			throw new IllegalStateException("Unable to start triple store because port 9999 is blocked!");
     		}
     	}
     }

     private void removeBlazegraphJournal()
     {
     	try
     	{
     		Files.deleteIfExists(Paths.get(JOURNAL_FILE_NAME));
     	}
     	catch (IOException e)
     	{
     		logger.info("Exception caught during removal of existing blazegraph journal file: " + JOURNAL_FILE_NAME);
     		e.printStackTrace();
     	}
     }

     private void startUp()
     {
     	Thread thread = new Thread(() -> {
     		try
     		{
     			boolean isDebug = java.lang.management.ManagementFactory.getRuntimeMXBean().getInputArguments().toString().indexOf("-agentlib:jdwp") > 0;

     			ProcessBuilder processBuilder = new ProcessBuilder();

     			if (isDebug)
     			{
     				processBuilder.command("java", //
     						"-server", //
     						"-Xmx4g", //
     						"-Dlog4j.configuration=file:" + TempFolderCreator.TRIPLE_STORE_FOLDER_PATH_NAME + "/bglog4j.properties", //
     						"-jar", //
     						"-Xdebug -Xnoagent -Djava.compiler=NONE -Xrunjdwp:transport=dt_socket,server=y,suspend=y,address=5005", //
     						TempFolderCreator.TRIPLE_STORE_FOLDER_PATH_NAME + "/blazegraph.jar");
     			}
     			else
     			{
     				processBuilder.command("java", //
     						"-server", //
     						"-Xmx4g", //
     						"-Dlog4j.configuration=file:" + TempFolderCreator.TRIPLE_STORE_FOLDER_PATH_NAME + "/bglog4j.properties", //
     						"-jar", //
     						TempFolderCreator.TRIPLE_STORE_FOLDER_PATH_NAME + "/blazegraph.jar");
     			}

     			processBuilder //
     					// .redirectOutput(System.out) //
     					// .redirectError(System.err) //
     					.directory(TempFolderCreator.TRIPLE_STORE_FOLDER_PATH.toFile());

     			Process blazegraphProcess = null;

     			try
     			{
     				blazegraphProcess = processBuilder.start();
     				blazegraphProcess.waitFor();
     				blazegraphProcess.destroyForcibly();
     			}
     			catch (InterruptedException | IOException e)
     			{
     				logger.info("Osee server exits, shutting down blazegraph as well. ", e);
     				if (blazegraphProcess != null)
     				{
     					blazegraphProcess.destroyForcibly();
     				}
     			}
     		}
     		catch (Exception e)
     		{
     			logger.info("Error during startup of Blazegraph.");
     			e.printStackTrace();
     		}
     	});
     	logger.info("Launching Blazegraph triple store in separate thread " + thread.getName());

     	thread.start();

     	logger.info("Waiting 2 secs to let Blazegraph start up then initializing.");
     	final ScheduledThreadPoolExecutor executor = new ScheduledThreadPoolExecutor(1);
     	executor.schedule(new Runnable()
     	{
     		@Override
     		public void run()
     		{
     			logger.info("Initializing triple store.");
     			BlazegraphTripleStore.initializeTripleStore();
     		}
     	}, 2000, TimeUnit.MILLISECONDS);
     }

     /*
      * Status request.
      */
     private static JettyResponseListener getStatus(RemoteRepositoryManager repo) throws Exception
     {
     	ConnectOptions opts = new ConnectOptions(sparqlEndPoint + "/status");
     	opts.method = "GET";
     	return repo.doConnect(opts);
     }

     public static void suppressTruthMaintenance(RemoteRepositoryManager repomanager) throws Exception
     {
     	String updateStr = "DISABLE ENTAILMENTS";
     	RemoteRepository repo = repomanager.getRepositoryForNamespace(datasetName);
     	repo.prepareUpdate(updateStr).evaluate();
     }

     public static void createGraph(RemoteRepositoryManager repo, String namespace, URI uri) throws Exception
     {
     	final StringBuilder update = new StringBuilder();
     	update.append(RdfUtil.getPrefixes());
     	update.append("CREATE GRAPH <" + uri + "> ");

     	BigdataSailRemoteRepository sailRepo = repo.getRepositoryForNamespace(datasetName).getBigdataSailRemoteRepository();
     	BigdataSailRemoteRepositoryConnection cxn = sailRepo.getConnection();

     	Update operation = cxn.prepareUpdate(QueryLanguage.SPARQL, update.toString());
     	operation.execute();
     	logger.info("Created graph " + uri + " in dataset " + datasetName);
     }

     private static long doInsertByBody(RemoteRepositoryManager repomanager, final String method, final Graph g, final URI defaultContext) throws Exception
     {
     	RemoteRepository repo = repomanager.getRepositoryForNamespace(datasetName);
     	final byte[] wireData = writeOnBuffer(RDFFormat.TURTLE, g);
     	final AddOp add = new AddOp(wireData, RDFFormat.TURTLE);
     	if (defaultContext != null)
     	{
     		add.setContext(defaultContext);
     	}
     	return repo.add(add);
     }

     static protected byte[] writeOnBuffer(final RDFFormat format, final Graph g) throws RDFHandlerException
     {
     	final RDFWriterFactory writerFactory = RDFWriterRegistry.getInstance().get(format);

     	if (writerFactory == null)
     	{
     		throw new IllegalStateException("RDFWriterFactory not found: format=" + format);
     	}

     	final ByteArrayOutputStream baos = new ByteArrayOutputStream();
     	final RDFWriter writer = writerFactory.getWriter(baos);
     	writer.startRDF();
     	for (Statement stmt : g)
     	{
     		writer.handleStatement(stmt);
     	}

     	writer.endRDF();
     	return baos.toByteArray();
     }

     /*
      * Get namespace properties.
      */
     private static JettyResponseListener getNamespaceProperties(RemoteRepositoryManager repo, String namespace) throws Exception
     {
     	ConnectOptions opts = new ConnectOptions(sparqlEndPoint + "/namespace/" + namespace + "/properties");
     	opts.method = "GET";
     	return repo.doConnect(opts);
     }

     /*
      * Load data into a namespace.
      */
     private static void loadDataFromFile(RemoteRepositoryManager repo, String namespace, String fileName)
     {

     	try (InputStream is = new FileInputStream(new File(fileName)))
     	{
     		repo.getRepositoryForNamespace(namespace).add(new RemoteRepository.AddOp(is, RDFFormat.TURTLE));
     	}
     	catch (Exception e)
     	{
     		logger.info("Error reading from file: " + fileName);
     		e.printStackTrace();
     	}
     }

     /*
      * Load data into a namespace.
      */
     private static void loadDataFromModel(RemoteRepositoryManager repo, String namespace, Model model)
     {
     	if (model == null || model.isEmpty())
     	{
     		logger.info("No triples found to be uploaded to triple store.");
     		return;
     	}

     	Path tempFilePath = null;
     	File tempFile = null;
     	try
     	{
     		tempFilePath = Files.createTempFile("triplestore-upload", "");
     		tempFile = tempFilePath.toFile();
     		try (FileOutputStream fos = new FileOutputStream(tempFile))
     		{
     			model.write(fos, "TTL");
     		}
     		catch (Exception e)
     		{
     			logger.info("Error during file upload to triple store.");
     			e.printStackTrace();
     		}
     	}
     	catch (IOException e)
     	{
     		logger.info("Error writing model to temp file for upload: " + tempFilePath.toAbsolutePath().toString());
     		e.printStackTrace();
     	}

     	try (InputStream is = new FileInputStream(tempFile))
     	{
     		repo.getRepositoryForNamespace(namespace).add(new RemoteRepository.AddOp(is, RDFFormat.TURTLE));
     	}
     	catch (Exception e)
     	{
     		logger.info("Error loading data to triple store from model.");
     		e.printStackTrace();
     	}
     }

     protected static Graph readGraphFromModel(Model model, String baseUri) throws RDFParseException, RDFHandlerException, IOException
     {
     	if (model == null || model.isEmpty())
     	{
     		return new LinkedHashModel();
     	}

     	Model tempModel = ModelFactory.createDefaultModel();
     	tempModel.add(model);

     	logger.info("Thread: " + Thread.currentThread().getName() + " transforming triples from jena to openrdf for graph " + baseUri);
     	StmtIterator stmtIterator = tempModel.listStatements();
     	List<org.openrdf.model.Statement> rdfStatements = new ArrayList<org.openrdf.model.Statement>();
     	while (stmtIterator.hasNext())
     	{
     		org.apache.jena.rdf.model.Statement jenaStatement = stmtIterator.next();
     		Statement rdfStatement = toOpenRdf(jenaStatement);
     		rdfStatements.add(rdfStatement);
     	}
     	tempModel = null;
     	final Graph g = new LinkedHashModel();
     	g.addAll(rdfStatements);
     	return g;
     }

     private static Statement toOpenRdf(org.apache.jena.rdf.model.Statement statement)
     {
     	org.apache.jena.rdf.model.Resource subject = statement.getSubject();
     	org.apache.jena.rdf.model.Property predicate = statement.getPredicate();
     	RDFNode object = statement.getObject();

     	ValueFactoryImpl valueFactory = org.openrdf.model.impl.ValueFactoryImpl.getInstance();
     	Statement rdfStatement = null;
     	if (subject.isURIResource())
     	{
     		if (object.isLiteral())
     		{
     			rdfStatement = valueFactory.createStatement(valueFactory.createURI(subject.getURI()), valueFactory.createURI(predicate.getURI()),
     					createLiteralValue(valueFactory, object.asLiteral().getValue()));
     		}
     		else if (object.isURIResource())
     		{
     			rdfStatement = valueFactory.createStatement(valueFactory.createURI(subject.getURI()), valueFactory.createURI(predicate.getURI()), valueFactory.createURI(object.asResource().getURI()));
     		}
     		else
     		{
     			// object blank
     			rdfStatement = valueFactory.createStatement(valueFactory.createURI(subject.getURI()), valueFactory.createURI(predicate.getURI()),
     					valueFactory.createBNode(object.asNode().getBlankNodeLabel()));
     		}
     	}
     	else
     	{
     		// subject blank
     		if (object.isLiteral())
     		{
     			rdfStatement = valueFactory.createStatement(valueFactory.createBNode(subject.asNode().getBlankNodeLabel()), valueFactory.createURI(predicate.getURI()),
     					createLiteralValue(valueFactory, object.asLiteral().getValue()));
     		}
     		else if (object.isURIResource())
     		{
     			rdfStatement = valueFactory.createStatement(valueFactory.createBNode(subject.asNode().getBlankNodeLabel()), valueFactory.createURI(predicate.getURI()),
     					valueFactory.createURI(object.asResource().getURI()));
     		}
     		else
     		{
     			// object blank
     			rdfStatement = valueFactory.createStatement(valueFactory.createBNode(subject.asNode().getBlankNodeLabel()), valueFactory.createURI(predicate.getURI()),
     					valueFactory.createBNode(object.asNode().getBlankNodeLabel()));
     		}
     	}
     	return rdfStatement;
     }

     private static Value createLiteralValue(ValueFactoryImpl valueFactory, Object o)
     {
     	if (o instanceof String)
     	{
     		return valueFactory.createLiteral((String) o);
     	}
     	else if (o instanceof Double)
     	{
     		return valueFactory.createLiteral((Double) o);
     	}
     	else if (o instanceof Integer)
     	{
     		return valueFactory.createLiteral((Integer) o);
     	}
     	else if (o instanceof Long)
     	{
     		return valueFactory.createLiteral((Long) o);
     	}
     	else if (o instanceof Float)
     	{
     		return valueFactory.createLiteral((Float) o);
     	}
     	else if (o instanceof Date)
     	{
     		return valueFactory.createLiteral((Date) o);
     	}
     	else if (o instanceof Boolean)
     	{
     		return valueFactory.createLiteral((Boolean) o);
     	}
     	else if (o instanceof Byte)
     	{
     		return valueFactory.createLiteral((Byte) o);
     	}
     	else if (o instanceof Short)
     	{
     		return valueFactory.createLiteral((Short) o);
     	}
     	else if (o instanceof XMLGregorianCalendar)
     	{
     		return valueFactory.createLiteral((XMLGregorianCalendar) o);
     	}
     	else if (o instanceof org.apache.jena.datatypes.xsd.XSDDateTime)
     	{
     		Calendar calendar = ((org.apache.jena.datatypes.xsd.XSDDateTime) o).asCalendar();
     		GregorianCalendar gregoriancalendar = new GregorianCalendar();
     		gregoriancalendar.setTime(calendar.getTime());
     		try
     		{
     			XMLGregorianCalendar xmlDate = DatatypeFactory.newInstance().newXMLGregorianCalendar(gregoriancalendar);
     			return valueFactory.createLiteral(xmlDate);
     		}
     		catch (DatatypeConfigurationException e)
     		{
     			logger.info("Error during transformation from XSDDateTime to XMLGregorianCalendar for value: " + String.valueOf(o) + " using string as default.");
     			return valueFactory.createLiteral(String.valueOf(o));
     		}
     	}
     	else
     	{
     		logger.info("Unhandled datatype for conversion from jena to openrdf for value: " + String.valueOf(o) + " using string as default.");
     		return valueFactory.createLiteral((String) o);
     	}
     }

     public static void startInNewThread()
     {
     	try
     	{
     		class BlazeLoaderThread extends Thread
     		{
     			@Override
     			public void run()
     			{
     				BlazegraphTripleStore blazegraphTripleStore = new BlazegraphTripleStore();
     				blazegraphTripleStore.run();
     			}
     		}

     		BlazeLoaderThread loaderThread = new BlazeLoaderThread();
     		loaderThread.start();
     	}
     	catch (Exception e)
     	{
     		logger.info("Error during starting up triple store.");
     		e.printStackTrace();
     	}

     }

}

